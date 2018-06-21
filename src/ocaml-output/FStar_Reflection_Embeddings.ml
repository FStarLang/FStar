open Prims
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding) =
  let embed_bv rng bv =
    FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv
      FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
     in
  let unembed_bv w t =
    let uu____29 =
      let uu____30 = FStar_Syntax_Subst.compress t  in
      uu____30.FStar_Syntax_Syntax.n  in
    match uu____29 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____36 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____36
    | uu____37 ->
        (if w
         then
           (let uu____39 =
              let uu____44 =
                let uu____45 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded bv: %s" uu____45  in
              (FStar_Errors.Warning_NotEmbedded, uu____44)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____39)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv unembed_bv
    FStar_Reflection_Data.fstar_refl_bv
  
let (e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding)
  =
  let embed_binder rng b =
    FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
      FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
     in
  let unembed_binder w t =
    let uu____75 =
      let uu____76 = FStar_Syntax_Subst.compress t  in
      uu____76.FStar_Syntax_Syntax.n  in
    match uu____75 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____82 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____82
    | uu____83 ->
        (if w
         then
           (let uu____85 =
              let uu____90 =
                let uu____91 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded binder: %s" uu____91  in
              (FStar_Errors.Warning_NotEmbedded, uu____90)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____85)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_binder unembed_binder
    FStar_Reflection_Data.fstar_refl_binder
  
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
          let uu____138 = f x  in
          FStar_Util.bind_opt uu____138
            (fun x1  ->
               let uu____146 = mapM_opt f xs  in
               FStar_Util.bind_opt uu____146
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
        let uu____212 =
          mapM_opt
            (fun uu____229  ->
               match uu____229 with
               | (bv,b,e) ->
                   if b
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.NT (bv, e))
                   else
                     (let uu____252 = unembed_term w e  in
                      FStar_Util.bind_opt uu____252
                        (fun e1  ->
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.NT (bv, e1))))) aq1
           in
        FStar_Util.bind_opt uu____212
          (fun s  ->
             let uu____266 = FStar_Syntax_Subst.subst s t1  in
             FStar_Pervasives_Native.Some uu____266)
         in
      let uu____267 =
        let uu____268 = FStar_Syntax_Subst.compress t  in
        uu____268.FStar_Syntax_Syntax.n  in
      match uu____267 with
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes
      | uu____279 ->
          (if w
           then
             (let uu____281 =
                let uu____286 =
                  let uu____287 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not an embedded term: %s" uu____287  in
                (FStar_Errors.Warning_NotEmbedded, uu____286)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____281)
           else ();
           FStar_Pervasives_Native.None)
       in
    FStar_Syntax_Embeddings.mk_emb embed_term unembed_term
      FStar_Syntax_Syntax.t_term
  
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
    let uu___223_317 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___223_317.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___223_317.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____336 = FStar_Syntax_Util.head_and_args t1  in
    match uu____336 with
    | (hd1,args) ->
        let uu____381 =
          let uu____396 =
            let uu____397 = FStar_Syntax_Util.un_uinst hd1  in
            uu____397.FStar_Syntax_Syntax.n  in
          (uu____396, args)  in
        (match uu____381 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____450 ->
             (if w
              then
                (let uu____466 =
                   let uu____471 =
                     let uu____472 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____472
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____471)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____466)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_aqualv unembed_aqualv
    FStar_Reflection_Data.fstar_refl_aqualv
  
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_list e_binder 
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding) =
  let embed_fv rng fv =
    FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
      FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
     in
  let unembed_fv w t =
    let uu____504 =
      let uu____505 = FStar_Syntax_Subst.compress t  in
      uu____505.FStar_Syntax_Syntax.n  in
    match uu____504 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____511 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____511
    | uu____512 ->
        (if w
         then
           (let uu____514 =
              let uu____519 =
                let uu____520 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____520  in
              (FStar_Errors.Warning_NotEmbedded, uu____519)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____514)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_fv unembed_fv
    FStar_Reflection_Data.fstar_refl_fv
  
let (e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding) =
  let embed_comp rng c =
    FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
      FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
     in
  let unembed_comp w t =
    let uu____550 =
      let uu____551 = FStar_Syntax_Subst.compress t  in
      uu____551.FStar_Syntax_Syntax.n  in
    match uu____550 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____557 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____557
    | uu____558 ->
        (if w
         then
           (let uu____560 =
              let uu____565 =
                let uu____566 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____566  in
              (FStar_Errors.Warning_NotEmbedded, uu____565)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____560)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp unembed_comp
    FStar_Reflection_Data.fstar_refl_comp
  
let (e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
     in
  let unembed_env w t =
    let uu____596 =
      let uu____597 = FStar_Syntax_Subst.compress t  in
      uu____597.FStar_Syntax_Syntax.n  in
    match uu____596 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____603 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____603
    | uu____604 ->
        (if w
         then
           (let uu____606 =
              let uu____611 =
                let uu____612 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____612  in
              (FStar_Errors.Warning_NotEmbedded, uu____611)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____606)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_env unembed_env
    FStar_Reflection_Data.fstar_refl_env
  
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
          let uu____633 =
            let uu____638 =
              let uu____639 =
                let uu____648 =
                  let uu____649 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____649  in
                FStar_Syntax_Syntax.as_arg uu____648  in
              [uu____639]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____638
             in
          uu____633 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____669 =
            let uu____674 =
              let uu____675 =
                let uu____684 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____684  in
              [uu____675]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____674
             in
          uu____669 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___224_703 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___224_703.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___224_703.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____722 = FStar_Syntax_Util.head_and_args t1  in
    match uu____722 with
    | (hd1,args) ->
        let uu____767 =
          let uu____782 =
            let uu____783 = FStar_Syntax_Util.un_uinst hd1  in
            uu____783.FStar_Syntax_Syntax.n  in
          (uu____782, args)  in
        (match uu____767 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____857)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____892 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____892
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____901)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____936 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____936
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____943 ->
             (if w
              then
                (let uu____959 =
                   let uu____964 =
                     let uu____965 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____965
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____964)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____959)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____973  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____986 =
            let uu____991 =
              let uu____992 =
                let uu____1001 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1001  in
              [uu____992]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____991
             in
          uu____986 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1026 =
            let uu____1031 =
              let uu____1032 =
                let uu____1041 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1041  in
              let uu____1042 =
                let uu____1053 =
                  let uu____1062 =
                    let uu____1063 =
                      let uu____1068 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1068  in
                    FStar_Syntax_Embeddings.embed uu____1063 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1062  in
                [uu____1053]  in
              uu____1032 :: uu____1042  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1031
             in
          uu____1026 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1100 =
            let uu____1105 =
              let uu____1106 =
                let uu____1115 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1115  in
              [uu____1106]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1105
             in
          uu____1100 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1135 =
            let uu____1140 =
              let uu____1141 =
                let uu____1150 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1150  in
              [uu____1141]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1140
             in
          uu____1135 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1171 =
            let uu____1176 =
              let uu____1177 =
                let uu____1186 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1186  in
              let uu____1187 =
                let uu____1198 =
                  let uu____1207 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____1207  in
                [uu____1198]  in
              uu____1177 :: uu____1187  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1176
             in
          uu____1171 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1250 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1250 with
      | (hd1,args) ->
          let uu____1295 =
            let uu____1308 =
              let uu____1309 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1309.FStar_Syntax_Syntax.n  in
            (uu____1308, args)  in
          (match uu____1295 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1324)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1349 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____1349
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1358)::(ps,uu____1360)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1395 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1395
                 (fun f1  ->
                    let uu____1401 =
                      let uu____1406 =
                        let uu____1411 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1411  in
                      FStar_Syntax_Embeddings.unembed' w uu____1406 ps  in
                    FStar_Util.bind_opt uu____1401
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1428)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1453 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1453
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1462)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1487 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1487
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1496)::(t2,uu____1498)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1533 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1533
                 (fun bv1  ->
                    let uu____1539 =
                      FStar_Syntax_Embeddings.unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1539
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1546 ->
               (if w
                then
                  (let uu____1560 =
                     let uu____1565 =
                       let uu____1566 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1566
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1565)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1560)
                else ();
                FStar_Pervasives_Native.None))
       in
    FStar_Syntax_Embeddings.mk_emb embed_pattern unembed_pattern
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
    let uu____1585 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1585
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1599 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1599 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1621 =
            let uu____1626 =
              let uu____1627 =
                let uu____1636 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1636  in
              [uu____1627]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1626
             in
          uu____1621 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1656 =
            let uu____1661 =
              let uu____1662 =
                let uu____1671 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1671  in
              [uu____1662]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1661
             in
          uu____1656 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1691 =
            let uu____1696 =
              let uu____1697 =
                let uu____1706 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1706  in
              [uu____1697]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1696
             in
          uu____1691 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1727 =
            let uu____1732 =
              let uu____1733 =
                let uu____1742 =
                  let uu____1743 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1743 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1742  in
              let uu____1746 =
                let uu____1757 =
                  let uu____1766 =
                    let uu____1767 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1767 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1766  in
                [uu____1757]  in
              uu____1733 :: uu____1746  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1732
             in
          uu____1727 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1806 =
            let uu____1811 =
              let uu____1812 =
                let uu____1821 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1821  in
              let uu____1822 =
                let uu____1833 =
                  let uu____1842 =
                    let uu____1843 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1843 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1842  in
                [uu____1833]  in
              uu____1812 :: uu____1822  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1811
             in
          uu____1806 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____1874 =
            let uu____1879 =
              let uu____1880 =
                let uu____1889 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1889  in
              let uu____1890 =
                let uu____1901 =
                  let uu____1910 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____1910  in
                [uu____1901]  in
              uu____1880 :: uu____1890  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____1879
             in
          uu____1874 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____1938 =
            let uu____1943 =
              let uu____1944 =
                let uu____1953 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____1953  in
              [uu____1944]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____1943
             in
          uu____1938 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____1974 =
            let uu____1979 =
              let uu____1980 =
                let uu____1989 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1989  in
              let uu____1990 =
                let uu____2001 =
                  let uu____2010 =
                    let uu____2011 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2011 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2010  in
                [uu____2001]  in
              uu____1980 :: uu____1990  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____1979
             in
          uu____1974 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2041 =
            let uu____2046 =
              let uu____2047 =
                let uu____2056 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____2056  in
              [uu____2047]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2046
             in
          uu____2041 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2077 =
            let uu____2082 =
              let uu____2083 =
                let uu____2092 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2092  in
              let uu____2093 =
                let uu____2104 =
                  let uu____2113 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2113  in
                [uu____2104]  in
              uu____2083 :: uu____2093  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2082
             in
          uu____2077 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2148 =
            let uu____2153 =
              let uu____2154 =
                let uu____2163 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2163  in
              let uu____2164 =
                let uu____2175 =
                  let uu____2184 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____2184  in
                let uu____2185 =
                  let uu____2196 =
                    let uu____2205 =
                      let uu____2206 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____2206 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2205  in
                  let uu____2209 =
                    let uu____2220 =
                      let uu____2229 =
                        let uu____2230 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____2230 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2229  in
                    [uu____2220]  in
                  uu____2196 :: uu____2209  in
                uu____2175 :: uu____2185  in
              uu____2154 :: uu____2164  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2153
             in
          uu____2148 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2281 =
            let uu____2286 =
              let uu____2287 =
                let uu____2296 =
                  let uu____2297 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2297 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____2296  in
              let uu____2300 =
                let uu____2311 =
                  let uu____2320 =
                    let uu____2321 =
                      let uu____2330 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2330  in
                    FStar_Syntax_Embeddings.embed uu____2321 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2320  in
                [uu____2311]  in
              uu____2287 :: uu____2300  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2286
             in
          uu____2281 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2380 =
            let uu____2385 =
              let uu____2386 =
                let uu____2395 =
                  let uu____2396 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2396 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2395  in
              let uu____2399 =
                let uu____2410 =
                  let uu____2419 =
                    let uu____2420 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2420 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2419  in
                let uu____2423 =
                  let uu____2434 =
                    let uu____2443 =
                      let uu____2444 =
                        let uu____2449 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2449  in
                      FStar_Syntax_Embeddings.embed uu____2444 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2443  in
                  [uu____2434]  in
                uu____2410 :: uu____2423  in
              uu____2386 :: uu____2399  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2385
             in
          uu____2380 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2495 =
            let uu____2500 =
              let uu____2501 =
                let uu____2510 =
                  let uu____2511 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2511 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2510  in
              let uu____2514 =
                let uu____2525 =
                  let uu____2534 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2534  in
                let uu____2535 =
                  let uu____2546 =
                    let uu____2555 =
                      let uu____2556 =
                        let uu____2561 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2561  in
                      FStar_Syntax_Embeddings.embed uu____2556 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2555  in
                  [uu____2546]  in
                uu____2525 :: uu____2535  in
              uu____2501 :: uu____2514  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2500
             in
          uu____2495 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___225_2600 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___225_2600.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___225_2600.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2616 = FStar_Syntax_Util.head_and_args t  in
      match uu____2616 with
      | (hd1,args) ->
          let uu____2661 =
            let uu____2674 =
              let uu____2675 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2675.FStar_Syntax_Syntax.n  in
            (uu____2674, args)  in
          (match uu____2661 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2690)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2715 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2715
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2724)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2749 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2749
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2758)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2783 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2783
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____2792)::(r,uu____2794)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____2829 = FStar_Syntax_Embeddings.unembed' w e_term l
                  in
               FStar_Util.bind_opt uu____2829
                 (fun l1  ->
                    let uu____2835 =
                      FStar_Syntax_Embeddings.unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____2835
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2844)::(t1,uu____2846)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____2881 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____2881
                 (fun b1  ->
                    let uu____2887 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____2887
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2896)::(t1,uu____2898)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____2933 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____2933
                 (fun b1  ->
                    let uu____2939 =
                      FStar_Syntax_Embeddings.unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____2939
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2948)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____2973 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____2973
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2982)::(t1,uu____2984)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3019 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3019
                 (fun b1  ->
                    let uu____3025 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3025
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3034)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3059 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____3059
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3068)::(l,uu____3070)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3105 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3105
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3116)::(b,uu____3118)::(t1,uu____3120)::(t2,uu____3122)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3177 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3177
                 (fun r1  ->
                    let uu____3183 =
                      FStar_Syntax_Embeddings.unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3183
                      (fun b1  ->
                         let uu____3189 =
                           FStar_Syntax_Embeddings.unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3189
                           (fun t11  ->
                              let uu____3195 =
                                FStar_Syntax_Embeddings.unembed' w e_term t2
                                 in
                              FStar_Util.bind_opt uu____3195
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3204)::(brs,uu____3206)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3241 = FStar_Syntax_Embeddings.unembed' w e_term t1
                  in
               FStar_Util.bind_opt uu____3241
                 (fun t2  ->
                    let uu____3247 =
                      let uu____3252 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed' w uu____3252 brs  in
                    FStar_Util.bind_opt uu____3247
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3271)::(t1,uu____3273)::(tacopt,uu____3275)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3320 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3320
                 (fun e1  ->
                    let uu____3326 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3326
                      (fun t2  ->
                         let uu____3332 =
                           let uu____3337 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3337
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3332
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3356)::(c,uu____3358)::(tacopt,uu____3360)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3405 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3405
                 (fun e1  ->
                    let uu____3411 =
                      FStar_Syntax_Embeddings.unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3411
                      (fun c1  ->
                         let uu____3417 =
                           let uu____3422 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3422
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3417
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
           | uu____3456 ->
               (if w
                then
                  (let uu____3470 =
                     let uu____3475 =
                       let uu____3476 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3476
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3475)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3470)
                else ();
                FStar_Pervasives_Native.None))
       in
    FStar_Syntax_Embeddings.mk_emb embed_term_view unembed_term_view
      FStar_Reflection_Data.fstar_refl_term_view
  
let (e_term_view :
  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding) =
  e_term_view_aq [] 
let (e_bv_view :
  FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding) =
  let embed_bv_view rng bvv =
    let uu____3501 =
      let uu____3506 =
        let uu____3507 =
          let uu____3516 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3516  in
        let uu____3517 =
          let uu____3528 =
            let uu____3537 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3537  in
          let uu____3538 =
            let uu____3549 =
              let uu____3558 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____3558  in
            [uu____3549]  in
          uu____3528 :: uu____3538  in
        uu____3507 :: uu____3517  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3506
       in
    uu____3501 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3609 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3609 with
    | (hd1,args) ->
        let uu____3654 =
          let uu____3667 =
            let uu____3668 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3668.FStar_Syntax_Syntax.n  in
          (uu____3667, args)  in
        (match uu____3654 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3683)::(idx,uu____3685)::(s,uu____3687)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3732 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3732
               (fun nm1  ->
                  let uu____3738 =
                    FStar_Syntax_Embeddings.unembed' w
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____3738
                    (fun idx1  ->
                       let uu____3744 =
                         FStar_Syntax_Embeddings.unembed' w e_term s  in
                       FStar_Util.bind_opt uu____3744
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3751 ->
             (if w
              then
                (let uu____3765 =
                   let uu____3770 =
                     let uu____3771 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3771
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3770)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3765)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_Data.fstar_refl_bv_view
  
let (e_comp_view :
  FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding) =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_Data.C_Total (t,md) ->
        let uu____3792 =
          let uu____3797 =
            let uu____3798 =
              let uu____3807 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____3807  in
            let uu____3808 =
              let uu____3819 =
                let uu____3828 =
                  let uu____3829 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____3829 rng md  in
                FStar_Syntax_Syntax.as_arg uu____3828  in
              [uu____3819]  in
            uu____3798 :: uu____3808  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____3797
           in
        uu____3792 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____3867 =
          let uu____3872 =
            let uu____3873 =
              let uu____3882 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____3882  in
            let uu____3883 =
              let uu____3894 =
                let uu____3903 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____3903  in
              [uu____3894]  in
            uu____3873 :: uu____3883  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____3872
           in
        uu____3867 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___226_3930 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___226_3930.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___226_3930.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3947 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3947 with
    | (hd1,args) ->
        let uu____3992 =
          let uu____4005 =
            let uu____4006 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4006.FStar_Syntax_Syntax.n  in
          (uu____4005, args)  in
        (match uu____3992 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4021)::(md,uu____4023)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4058 = FStar_Syntax_Embeddings.unembed' w e_term t2
                in
             FStar_Util.bind_opt uu____4058
               (fun t3  ->
                  let uu____4064 =
                    let uu____4069 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed' w uu____4069 md  in
                  FStar_Util.bind_opt uu____4064
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4088)::(post,uu____4090)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4125 = FStar_Syntax_Embeddings.unembed' w e_term pre
                in
             FStar_Util.bind_opt uu____4125
               (fun pre1  ->
                  let uu____4131 =
                    FStar_Syntax_Embeddings.unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4131
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
         | uu____4155 ->
             (if w
              then
                (let uu____4169 =
                   let uu____4174 =
                     let uu____4175 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4175
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4174)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4169)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_Data.fstar_refl_comp_view
  
let (e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding) =
  let embed_order rng o =
    let r =
      match o with
      | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
      | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
      | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
    let uu___227_4195 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___227_4195.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___227_4195.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4214 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4214 with
    | (hd1,args) ->
        let uu____4259 =
          let uu____4274 =
            let uu____4275 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4275.FStar_Syntax_Syntax.n  in
          (uu____4274, args)  in
        (match uu____4259 with
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
         | uu____4347 ->
             (if w
              then
                (let uu____4363 =
                   let uu____4368 =
                     let uu____4369 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4369
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4368)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4363)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_order unembed_order
    FStar_Syntax_Syntax.t_order
  
let (e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding)
  =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
     in
  let unembed_sigelt w t =
    let uu____4399 =
      let uu____4400 = FStar_Syntax_Subst.compress t  in
      uu____4400.FStar_Syntax_Syntax.n  in
    match uu____4399 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____4406 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____4406
    | uu____4407 ->
        (if w
         then
           (let uu____4409 =
              let uu____4414 =
                let uu____4415 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4415
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4414)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4409)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt
  
let (e_sigelt_view :
  FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding) =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
        let uu____4434 =
          let uu____4439 =
            let uu____4440 =
              let uu____4449 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____4449  in
            let uu____4450 =
              let uu____4461 =
                let uu____4470 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____4470  in
              let uu____4471 =
                let uu____4482 =
                  let uu____4491 =
                    FStar_Syntax_Embeddings.embed e_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____4491  in
                let uu____4492 =
                  let uu____4503 =
                    let uu____4512 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____4512  in
                  [uu____4503]  in
                uu____4482 :: uu____4492  in
              uu____4461 :: uu____4471  in
            uu____4440 :: uu____4450  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4439
           in
        uu____4434 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4557 =
          let uu____4562 =
            let uu____4563 =
              let uu____4572 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4572  in
            let uu____4575 =
              let uu____4586 =
                let uu____4595 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____4595  in
              [uu____4586]  in
            uu____4563 :: uu____4575  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____4562
           in
        uu____4557 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____4634 =
          let uu____4639 =
            let uu____4640 =
              let uu____4649 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4649  in
            let uu____4652 =
              let uu____4663 =
                let uu____4672 =
                  FStar_Syntax_Embeddings.embed e_binders rng bs  in
                FStar_Syntax_Syntax.as_arg uu____4672  in
              let uu____4673 =
                let uu____4684 =
                  let uu____4693 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____4693  in
                let uu____4694 =
                  let uu____4705 =
                    let uu____4714 =
                      let uu____4715 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_string_list
                         in
                      FStar_Syntax_Embeddings.embed uu____4715 rng dcs  in
                    FStar_Syntax_Syntax.as_arg uu____4714  in
                  [uu____4705]  in
                uu____4684 :: uu____4694  in
              uu____4663 :: uu____4673  in
            uu____4640 :: uu____4652  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____4639
           in
        uu____4634 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___228_4770 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___228_4770.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___228_4770.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4787 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4787 with
    | (hd1,args) ->
        let uu____4832 =
          let uu____4845 =
            let uu____4846 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4846.FStar_Syntax_Syntax.n  in
          (uu____4845, args)  in
        (match uu____4832 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____4861)::(bs,uu____4863)::(t2,uu____4865)::(dcs,uu____4867)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____4922 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____4922
               (fun nm1  ->
                  let uu____4936 =
                    FStar_Syntax_Embeddings.unembed' w e_binders bs  in
                  FStar_Util.bind_opt uu____4936
                    (fun bs1  ->
                       let uu____4942 =
                         FStar_Syntax_Embeddings.unembed' w e_term t2  in
                       FStar_Util.bind_opt uu____4942
                         (fun t3  ->
                            let uu____4948 =
                              let uu____4955 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_string_list
                                 in
                              FStar_Syntax_Embeddings.unembed' w uu____4955
                                dcs
                               in
                            FStar_Util.bind_opt uu____4948
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_42  ->
                                      FStar_Pervasives_Native.Some _0_42)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____4986)::(fvar1,uu____4988)::(ty,uu____4990)::(t2,uu____4992)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5047 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____5047
               (fun r1  ->
                  let uu____5053 =
                    FStar_Syntax_Embeddings.unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5053
                    (fun fvar2  ->
                       let uu____5059 =
                         FStar_Syntax_Embeddings.unembed' w e_term ty  in
                       FStar_Util.bind_opt uu____5059
                         (fun ty1  ->
                            let uu____5065 =
                              FStar_Syntax_Embeddings.unembed' w e_term t2
                               in
                            FStar_Util.bind_opt uu____5065
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
         | uu____5087 ->
             (if w
              then
                (let uu____5101 =
                   let uu____5106 =
                     let uu____5107 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5107
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5106)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5101)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_Data.fstar_refl_sigelt_view
  
let (e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding) =
  let rec embed_exp rng e =
    let r =
      match e with
      | FStar_Reflection_Data.Unit  ->
          FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
      | FStar_Reflection_Data.Var i ->
          let uu____5128 =
            let uu____5133 =
              let uu____5134 =
                let uu____5143 =
                  let uu____5144 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5144  in
                FStar_Syntax_Syntax.as_arg uu____5143  in
              [uu____5134]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5133
             in
          uu____5128 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5165 =
            let uu____5170 =
              let uu____5171 =
                let uu____5180 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5180  in
              let uu____5181 =
                let uu____5192 =
                  let uu____5201 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5201  in
                [uu____5192]  in
              uu____5171 :: uu____5181  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5170
             in
          uu____5165 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___229_5228 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___229_5228.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___229_5228.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5247 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5247 with
    | (hd1,args) ->
        let uu____5292 =
          let uu____5305 =
            let uu____5306 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5306.FStar_Syntax_Syntax.n  in
          (uu____5305, args)  in
        (match uu____5292 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5336)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5361 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____5361
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5370)::(e2,uu____5372)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5407 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5407
               (fun e11  ->
                  let uu____5413 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5413
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5420 ->
             (if w
              then
                (let uu____5434 =
                   let uu____5439 =
                     let uu____5440 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5440
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5439)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5434)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp
    FStar_Reflection_Data.fstar_refl_exp
  
let (e_binder_view :
  FStar_Reflection_Data.binder_view FStar_Syntax_Embeddings.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv 
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let bv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5450 =
      let uu____5455 =
        let uu____5456 =
          let uu____5465 =
            let uu____5466 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____5466
             in
          FStar_Syntax_Syntax.as_arg uu____5465  in
        [uu____5456]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____5455
       in
    uu____5450 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5491 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____5491 with
    | (bv,aq) ->
        let uu____5498 =
          let uu____5503 =
            let uu____5504 =
              let uu____5513 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____5513  in
            let uu____5514 =
              let uu____5525 =
                let uu____5534 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____5534  in
              [uu____5525]  in
            uu____5504 :: uu____5514  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____5503
           in
        uu____5498 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5567 =
      let uu____5572 =
        let uu____5573 =
          let uu____5582 =
            let uu____5583 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____5588 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____5583
              i.FStar_Syntax_Syntax.rng uu____5588
             in
          FStar_Syntax_Syntax.as_arg uu____5582  in
        [uu____5573]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____5572
       in
    uu____5567 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5617 =
      let uu____5622 =
        let uu____5623 =
          let uu____5632 =
            let uu____5633 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____5633
             in
          FStar_Syntax_Syntax.as_arg uu____5632  in
        [uu____5623]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____5622
       in
    uu____5617 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5663 =
      let uu____5668 =
        let uu____5669 =
          let uu____5678 =
            let uu____5679 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____5679
             in
          FStar_Syntax_Syntax.as_arg uu____5678  in
        [uu____5669]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____5668
       in
    uu____5663 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  