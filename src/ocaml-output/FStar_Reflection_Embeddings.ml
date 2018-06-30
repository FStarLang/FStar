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
      | uu____347 -> FStar_Pervasives_Native.None  in
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
          let uu____390 =
            let uu____395 =
              let uu____396 =
                let uu____405 = FStar_Syntax_Embeddings.embed e_term rng t
                   in
                FStar_Syntax_Syntax.as_arg uu____405  in
              [uu____396]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.t
              uu____395
             in
          uu____390 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___225_424 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___225_424.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___225_424.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_aqualv w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____443 = FStar_Syntax_Util.head_and_args t1  in
    match uu____443 with
    | (hd1,args) ->
        let uu____488 =
          let uu____503 =
            let uu____504 = FStar_Syntax_Util.un_uinst hd1  in
            uu____504.FStar_Syntax_Syntax.n  in
          (uu____503, args)  in
        (match uu____488 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____559)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid
             ->
             let uu____594 = FStar_Syntax_Embeddings.unembed' w e_term t2  in
             FStar_Util.bind_opt uu____594
               (fun t3  ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_Data.Q_Meta t3))
         | uu____599 ->
             (if w
              then
                (let uu____615 =
                   let uu____620 =
                     let uu____621 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.format1 "Not an embedded aqualv: %s"
                       uu____621
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____620)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____615)
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
    let uu____653 =
      let uu____654 = FStar_Syntax_Subst.compress t  in
      uu____654.FStar_Syntax_Syntax.n  in
    match uu____653 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____660 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____660
    | uu____661 ->
        (if w
         then
           (let uu____663 =
              let uu____668 =
                let uu____669 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded fvar: %s" uu____669  in
              (FStar_Errors.Warning_NotEmbedded, uu____668)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____663)
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
    let uu____699 =
      let uu____700 = FStar_Syntax_Subst.compress t  in
      uu____700.FStar_Syntax_Syntax.n  in
    match uu____699 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____706 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____706
    | uu____707 ->
        (if w
         then
           (let uu____709 =
              let uu____714 =
                let uu____715 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded comp: %s" uu____715  in
              (FStar_Errors.Warning_NotEmbedded, uu____714)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____709)
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
    let uu____745 =
      let uu____746 = FStar_Syntax_Subst.compress t  in
      uu____746.FStar_Syntax_Syntax.n  in
    match uu____745 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____752 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____752
    | uu____753 ->
        (if w
         then
           (let uu____755 =
              let uu____760 =
                let uu____761 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded env: %s" uu____761  in
              (FStar_Errors.Warning_NotEmbedded, uu____760)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____755)
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
          let uu____782 =
            let uu____787 =
              let uu____788 =
                let uu____797 =
                  let uu____798 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____798  in
                FStar_Syntax_Syntax.as_arg uu____797  in
              [uu____788]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
              uu____787
             in
          uu____782 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.C_String s ->
          let uu____818 =
            let uu____823 =
              let uu____824 =
                let uu____833 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string rng s
                   in
                FStar_Syntax_Syntax.as_arg uu____833  in
              [uu____824]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
              uu____823
             in
          uu____818 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___226_852 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___226_852.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___226_852.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_const w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____871 = FStar_Syntax_Util.head_and_args t1  in
    match uu____871 with
    | (hd1,args) ->
        let uu____916 =
          let uu____931 =
            let uu____932 = FStar_Syntax_Util.un_uinst hd1  in
            uu____932.FStar_Syntax_Syntax.n  in
          (uu____931, args)  in
        (match uu____916 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1006)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1041 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____1041
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1050)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1085 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string s
                in
             FStar_Util.bind_opt uu____1085
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1092 ->
             (if w
              then
                (let uu____1108 =
                   let uu____1113 =
                     let uu____1114 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded vconst: %s"
                       uu____1114
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1113)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1108)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_const unembed_const
    FStar_Reflection_Data.fstar_refl_vconst
  
let rec (e_pattern' :
  unit -> FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding) =
  fun uu____1122  ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____1135 =
            let uu____1140 =
              let uu____1141 =
                let uu____1150 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____1150  in
              [uu____1141]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____1140
             in
          uu____1135 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____1175 =
            let uu____1180 =
              let uu____1181 =
                let uu____1190 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1190  in
              let uu____1191 =
                let uu____1202 =
                  let uu____1211 =
                    let uu____1212 =
                      let uu____1217 = e_pattern' ()  in
                      FStar_Syntax_Embeddings.e_list uu____1217  in
                    FStar_Syntax_Embeddings.embed uu____1212 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____1211  in
                [uu____1202]  in
              uu____1181 :: uu____1191  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____1180
             in
          uu____1175 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____1249 =
            let uu____1254 =
              let uu____1255 =
                let uu____1264 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1264  in
              [uu____1255]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____1254
             in
          uu____1249 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____1284 =
            let uu____1289 =
              let uu____1290 =
                let uu____1299 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1299  in
              [uu____1290]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____1289
             in
          uu____1284 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Dot_Term (bv,t) ->
          let uu____1320 =
            let uu____1325 =
              let uu____1326 =
                let uu____1335 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1335  in
              let uu____1336 =
                let uu____1347 =
                  let uu____1356 = FStar_Syntax_Embeddings.embed e_term rng t
                     in
                  FStar_Syntax_Syntax.as_arg uu____1356  in
                [uu____1347]  in
              uu____1326 :: uu____1336  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t
              uu____1325
             in
          uu____1320 FStar_Pervasives_Native.None rng
       in
    let rec unembed_pattern w t =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let uu____1399 = FStar_Syntax_Util.head_and_args t1  in
      match uu____1399 with
      | (hd1,args) ->
          let uu____1444 =
            let uu____1457 =
              let uu____1458 = FStar_Syntax_Util.un_uinst hd1  in
              uu____1458.FStar_Syntax_Syntax.n  in
            (uu____1457, args)  in
          (match uu____1444 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1473)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
               ->
               let uu____1498 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____1498
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                      (FStar_Reflection_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(f,uu____1507)::(ps,uu____1509)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
               ->
               let uu____1544 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____1544
                 (fun f1  ->
                    let uu____1550 =
                      let uu____1555 =
                        let uu____1560 = e_pattern' ()  in
                        FStar_Syntax_Embeddings.e_list uu____1560  in
                      FStar_Syntax_Embeddings.unembed' w uu____1555 ps  in
                    FStar_Util.bind_opt uu____1550
                      (fun ps1  ->
                         FStar_All.pipe_left
                           (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                           (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1577)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
               ->
               let uu____1602 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1602
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                      (FStar_Reflection_Data.Pat_Var bv1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1611)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
               ->
               let uu____1636 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1636
                 (fun bv1  ->
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_Pervasives_Native.Some _0_21)
                      (FStar_Reflection_Data.Pat_Wild bv1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(bv,uu____1645)::(t2,uu____1647)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid
               ->
               let uu____1682 = FStar_Syntax_Embeddings.unembed' w e_bv bv
                  in
               FStar_Util.bind_opt uu____1682
                 (fun bv1  ->
                    let uu____1688 =
                      FStar_Syntax_Embeddings.unembed' w e_term t2  in
                    FStar_Util.bind_opt uu____1688
                      (fun t3  ->
                         FStar_All.pipe_left
                           (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                           (FStar_Reflection_Data.Pat_Dot_Term (bv1, t3))))
           | uu____1695 ->
               (if w
                then
                  (let uu____1709 =
                     let uu____1714 =
                       let uu____1715 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1 "Not an embedded pattern: %s"
                         uu____1715
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____1714)  in
                   FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
                     uu____1709)
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
    let uu____1734 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1734
  
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let uu____1748 = e_term_aq aq  in
    FStar_Syntax_Embeddings.e_tuple2 uu____1748 e_aqualv
  
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding)
  =
  fun aq  ->
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____1770 =
            let uu____1775 =
              let uu____1776 =
                let uu____1785 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1785  in
              [uu____1776]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____1775
             in
          uu____1770 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____1805 =
            let uu____1810 =
              let uu____1811 =
                let uu____1820 = FStar_Syntax_Embeddings.embed e_bv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____1820  in
              [uu____1811]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____1810
             in
          uu____1805 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____1840 =
            let uu____1845 =
              let uu____1846 =
                let uu____1855 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____1855  in
              [uu____1846]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____1845
             in
          uu____1840 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____1876 =
            let uu____1881 =
              let uu____1882 =
                let uu____1891 =
                  let uu____1892 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____1892 rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____1891  in
              let uu____1895 =
                let uu____1906 =
                  let uu____1915 =
                    let uu____1916 = e_argv_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1916 rng a  in
                  FStar_Syntax_Syntax.as_arg uu____1915  in
                [uu____1906]  in
              uu____1882 :: uu____1895  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____1881
             in
          uu____1876 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____1955 =
            let uu____1960 =
              let uu____1961 =
                let uu____1970 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____1970  in
              let uu____1971 =
                let uu____1982 =
                  let uu____1991 =
                    let uu____1992 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____1992 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____1991  in
                [uu____1982]  in
              uu____1961 :: uu____1971  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____1960
             in
          uu____1955 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____2023 =
            let uu____2028 =
              let uu____2029 =
                let uu____2038 = FStar_Syntax_Embeddings.embed e_binder rng b
                   in
                FStar_Syntax_Syntax.as_arg uu____2038  in
              let uu____2039 =
                let uu____2050 =
                  let uu____2059 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2059  in
                [uu____2050]  in
              uu____2029 :: uu____2039  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____2028
             in
          uu____2023 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____2087 =
            let uu____2092 =
              let uu____2093 =
                let uu____2102 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_unit rng ()
                   in
                FStar_Syntax_Syntax.as_arg uu____2102  in
              [uu____2093]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____2092
             in
          uu____2087 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____2123 =
            let uu____2128 =
              let uu____2129 =
                let uu____2138 = FStar_Syntax_Embeddings.embed e_bv rng bv
                   in
                FStar_Syntax_Syntax.as_arg uu____2138  in
              let uu____2139 =
                let uu____2150 =
                  let uu____2159 =
                    let uu____2160 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2160 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2159  in
                [uu____2150]  in
              uu____2129 :: uu____2139  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____2128
             in
          uu____2123 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____2190 =
            let uu____2195 =
              let uu____2196 =
                let uu____2205 = FStar_Syntax_Embeddings.embed e_const rng c
                   in
                FStar_Syntax_Syntax.as_arg uu____2205  in
              [uu____2196]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____2195
             in
          uu____2190 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,d) ->
          let uu____2226 =
            let uu____2231 =
              let uu____2232 =
                let uu____2241 =
                  FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int
                    rng u
                   in
                FStar_Syntax_Syntax.as_arg uu____2241  in
              let uu____2242 =
                let uu____2253 =
                  let uu____2262 =
                    FStar_Syntax_Util.mk_lazy (u, d)
                      FStar_Syntax_Util.t_ctx_uvar_and_sust
                      FStar_Syntax_Syntax.Lazy_uvar
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.as_arg uu____2262  in
                [uu____2253]  in
              uu____2232 :: uu____2242  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____2231
             in
          uu____2226 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____2297 =
            let uu____2302 =
              let uu____2303 =
                let uu____2312 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_bool rng r
                   in
                FStar_Syntax_Syntax.as_arg uu____2312  in
              let uu____2313 =
                let uu____2324 =
                  let uu____2333 = FStar_Syntax_Embeddings.embed e_bv rng b
                     in
                  FStar_Syntax_Syntax.as_arg uu____2333  in
                let uu____2334 =
                  let uu____2345 =
                    let uu____2354 =
                      let uu____2355 = e_term_aq aq  in
                      FStar_Syntax_Embeddings.embed uu____2355 rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____2354  in
                  let uu____2358 =
                    let uu____2369 =
                      let uu____2378 =
                        let uu____2379 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.embed uu____2379 rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____2378  in
                    [uu____2369]  in
                  uu____2345 :: uu____2358  in
                uu____2324 :: uu____2334  in
              uu____2303 :: uu____2313  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____2302
             in
          uu____2297 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____2430 =
            let uu____2435 =
              let uu____2436 =
                let uu____2445 =
                  let uu____2446 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2446 rng t1  in
                FStar_Syntax_Syntax.as_arg uu____2445  in
              let uu____2449 =
                let uu____2460 =
                  let uu____2469 =
                    let uu____2470 =
                      let uu____2479 = e_branch_aq aq  in
                      FStar_Syntax_Embeddings.e_list uu____2479  in
                    FStar_Syntax_Embeddings.embed uu____2470 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____2469  in
                [uu____2460]  in
              uu____2436 :: uu____2449  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____2435
             in
          uu____2430 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedT (e,t1,tacopt) ->
          let uu____2529 =
            let uu____2534 =
              let uu____2535 =
                let uu____2544 =
                  let uu____2545 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2545 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2544  in
              let uu____2548 =
                let uu____2559 =
                  let uu____2568 =
                    let uu____2569 = e_term_aq aq  in
                    FStar_Syntax_Embeddings.embed uu____2569 rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____2568  in
                let uu____2572 =
                  let uu____2583 =
                    let uu____2592 =
                      let uu____2593 =
                        let uu____2598 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2598  in
                      FStar_Syntax_Embeddings.embed uu____2593 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2592  in
                  [uu____2583]  in
                uu____2559 :: uu____2572  in
              uu____2535 :: uu____2548  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t
              uu____2534
             in
          uu____2529 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
          let uu____2644 =
            let uu____2649 =
              let uu____2650 =
                let uu____2659 =
                  let uu____2660 = e_term_aq aq  in
                  FStar_Syntax_Embeddings.embed uu____2660 rng e  in
                FStar_Syntax_Syntax.as_arg uu____2659  in
              let uu____2663 =
                let uu____2674 =
                  let uu____2683 = FStar_Syntax_Embeddings.embed e_comp rng c
                     in
                  FStar_Syntax_Syntax.as_arg uu____2683  in
                let uu____2684 =
                  let uu____2695 =
                    let uu____2704 =
                      let uu____2705 =
                        let uu____2710 = e_term_aq aq  in
                        FStar_Syntax_Embeddings.e_option uu____2710  in
                      FStar_Syntax_Embeddings.embed uu____2705 rng tacopt  in
                    FStar_Syntax_Syntax.as_arg uu____2704  in
                  [uu____2695]  in
                uu____2674 :: uu____2684  in
              uu____2650 :: uu____2663  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t
              uu____2649
             in
          uu____2644 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___227_2749 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___227_2749.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars =
              (uu___227_2749.FStar_Syntax_Syntax.vars)
          }
       in
    let unembed_term_view w t =
      let uu____2765 = FStar_Syntax_Util.head_and_args t  in
      match uu____2765 with
      | (hd1,args) ->
          let uu____2810 =
            let uu____2823 =
              let uu____2824 = FStar_Syntax_Util.un_uinst hd1  in
              uu____2824.FStar_Syntax_Syntax.n  in
            (uu____2823, args)  in
          (match uu____2810 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2839)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
               ->
               let uu____2864 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2864
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_23  -> FStar_Pervasives_Native.Some _0_23)
                      (FStar_Reflection_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2873)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
               ->
               let uu____2898 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____2898
                 (fun b1  ->
                    FStar_All.pipe_left
                      (fun _0_24  -> FStar_Pervasives_Native.Some _0_24)
                      (FStar_Reflection_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____2907)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
               ->
               let uu____2932 = FStar_Syntax_Embeddings.unembed' w e_fv f  in
               FStar_Util.bind_opt uu____2932
                 (fun f1  ->
                    FStar_All.pipe_left
                      (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                      (FStar_Reflection_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(l,uu____2941)::(r,uu____2943)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
               ->
               let uu____2978 = FStar_Syntax_Embeddings.unembed' w e_term l
                  in
               FStar_Util.bind_opt uu____2978
                 (fun l1  ->
                    let uu____2984 =
                      FStar_Syntax_Embeddings.unembed' w e_argv r  in
                    FStar_Util.bind_opt uu____2984
                      (fun r1  ->
                         FStar_All.pipe_left
                           (fun _0_26  -> FStar_Pervasives_Native.Some _0_26)
                           (FStar_Reflection_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____2993)::(t1,uu____2995)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
               ->
               let uu____3030 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____3030
                 (fun b1  ->
                    let uu____3036 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3036
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                           (FStar_Reflection_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3045)::(t1,uu____3047)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
               ->
               let uu____3082 = FStar_Syntax_Embeddings.unembed' w e_binder b
                  in
               FStar_Util.bind_opt uu____3082
                 (fun b1  ->
                    let uu____3088 =
                      FStar_Syntax_Embeddings.unembed' w e_comp t1  in
                    FStar_Util.bind_opt uu____3088
                      (fun c  ->
                         FStar_All.pipe_left
                           (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                           (FStar_Reflection_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____3097)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
               ->
               let uu____3122 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_unit u
                  in
               FStar_Util.bind_opt uu____3122
                 (fun u1  ->
                    FStar_All.pipe_left
                      (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                      (FStar_Reflection_Data.Tv_Type ()))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(b,uu____3131)::(t1,uu____3133)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
               ->
               let uu____3168 = FStar_Syntax_Embeddings.unembed' w e_bv b  in
               FStar_Util.bind_opt uu____3168
                 (fun b1  ->
                    let uu____3174 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3174
                      (fun t2  ->
                         FStar_All.pipe_left
                           (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
                           (FStar_Reflection_Data.Tv_Refine (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3183)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
               ->
               let uu____3208 = FStar_Syntax_Embeddings.unembed' w e_const c
                  in
               FStar_Util.bind_opt uu____3208
                 (fun c1  ->
                    FStar_All.pipe_left
                      (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                      (FStar_Reflection_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(u,uu____3217)::(l,uu____3219)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
               ->
               let uu____3254 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_int u
                  in
               FStar_Util.bind_opt uu____3254
                 (fun u1  ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l
                       in
                    FStar_All.pipe_left
                      (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      (FStar_Reflection_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(r,uu____3265)::(b,uu____3267)::(t1,uu____3269)::(t2,uu____3271)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
               ->
               let uu____3326 =
                 FStar_Syntax_Embeddings.unembed' w
                   FStar_Syntax_Embeddings.e_bool r
                  in
               FStar_Util.bind_opt uu____3326
                 (fun r1  ->
                    let uu____3332 =
                      FStar_Syntax_Embeddings.unembed' w e_bv b  in
                    FStar_Util.bind_opt uu____3332
                      (fun b1  ->
                         let uu____3338 =
                           FStar_Syntax_Embeddings.unembed' w e_term t1  in
                         FStar_Util.bind_opt uu____3338
                           (fun t11  ->
                              let uu____3344 =
                                FStar_Syntax_Embeddings.unembed' w e_term t2
                                 in
                              FStar_Util.bind_opt uu____3344
                                (fun t21  ->
                                   FStar_All.pipe_left
                                     (fun _0_33  ->
                                        FStar_Pervasives_Native.Some _0_33)
                                     (FStar_Reflection_Data.Tv_Let
                                        (r1, b1, t11, t21))))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(t1,uu____3353)::(brs,uu____3355)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
               ->
               let uu____3390 = FStar_Syntax_Embeddings.unembed' w e_term t1
                  in
               FStar_Util.bind_opt uu____3390
                 (fun t2  ->
                    let uu____3396 =
                      let uu____3401 =
                        FStar_Syntax_Embeddings.e_list e_branch  in
                      FStar_Syntax_Embeddings.unembed' w uu____3401 brs  in
                    FStar_Util.bind_opt uu____3396
                      (fun brs1  ->
                         FStar_All.pipe_left
                           (fun _0_34  -> FStar_Pervasives_Native.Some _0_34)
                           (FStar_Reflection_Data.Tv_Match (t2, brs1))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3420)::(t1,uu____3422)::(tacopt,uu____3424)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid
               ->
               let uu____3469 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3469
                 (fun e1  ->
                    let uu____3475 =
                      FStar_Syntax_Embeddings.unembed' w e_term t1  in
                    FStar_Util.bind_opt uu____3475
                      (fun t2  ->
                         let uu____3481 =
                           let uu____3486 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3486
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3481
                           (fun tacopt1  ->
                              FStar_All.pipe_left
                                (fun _0_35  ->
                                   FStar_Pervasives_Native.Some _0_35)
                                (FStar_Reflection_Data.Tv_AscribedT
                                   (e1, t2, tacopt1)))))
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(e,uu____3505)::(c,uu____3507)::(tacopt,uu____3509)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid
               ->
               let uu____3554 = FStar_Syntax_Embeddings.unembed' w e_term e
                  in
               FStar_Util.bind_opt uu____3554
                 (fun e1  ->
                    let uu____3560 =
                      FStar_Syntax_Embeddings.unembed' w e_comp c  in
                    FStar_Util.bind_opt uu____3560
                      (fun c1  ->
                         let uu____3566 =
                           let uu____3571 =
                             FStar_Syntax_Embeddings.e_option e_term  in
                           FStar_Syntax_Embeddings.unembed' w uu____3571
                             tacopt
                            in
                         FStar_Util.bind_opt uu____3566
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
           | uu____3605 ->
               (if w
                then
                  (let uu____3619 =
                     let uu____3624 =
                       let uu____3625 = FStar_Syntax_Print.term_to_string t
                          in
                       FStar_Util.format1 "Not an embedded term_view: %s"
                         uu____3625
                        in
                     (FStar_Errors.Warning_NotEmbedded, uu____3624)  in
                   FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                     uu____3619)
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
    let uu____3650 =
      let uu____3655 =
        let uu____3656 =
          let uu____3665 =
            FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string
              rng bvv.FStar_Reflection_Data.bv_ppname
             in
          FStar_Syntax_Syntax.as_arg uu____3665  in
        let uu____3666 =
          let uu____3677 =
            let uu____3686 =
              FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
                bvv.FStar_Reflection_Data.bv_index
               in
            FStar_Syntax_Syntax.as_arg uu____3686  in
          let uu____3687 =
            let uu____3698 =
              let uu____3707 =
                FStar_Syntax_Embeddings.embed e_term rng
                  bvv.FStar_Reflection_Data.bv_sort
                 in
              FStar_Syntax_Syntax.as_arg uu____3707  in
            [uu____3698]  in
          uu____3677 :: uu____3687  in
        uu____3656 :: uu____3666  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3655
       in
    uu____3650 FStar_Pervasives_Native.None rng  in
  let unembed_bv_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3758 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3758 with
    | (hd1,args) ->
        let uu____3803 =
          let uu____3816 =
            let uu____3817 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3817.FStar_Syntax_Syntax.n  in
          (uu____3816, args)  in
        (match uu____3803 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3832)::(idx,uu____3834)::(s,uu____3836)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____3881 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string nm
                in
             FStar_Util.bind_opt uu____3881
               (fun nm1  ->
                  let uu____3887 =
                    FStar_Syntax_Embeddings.unembed' w
                      FStar_Syntax_Embeddings.e_int idx
                     in
                  FStar_Util.bind_opt uu____3887
                    (fun idx1  ->
                       let uu____3893 =
                         FStar_Syntax_Embeddings.unembed' w e_term s  in
                       FStar_Util.bind_opt uu____3893
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_38  ->
                                 FStar_Pervasives_Native.Some _0_38)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____3900 ->
             (if w
              then
                (let uu____3914 =
                   let uu____3919 =
                     let uu____3920 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded bv_view: %s"
                       uu____3920
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____3919)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3914)
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
        let uu____3941 =
          let uu____3946 =
            let uu____3947 =
              let uu____3956 = FStar_Syntax_Embeddings.embed e_term rng t  in
              FStar_Syntax_Syntax.as_arg uu____3956  in
            let uu____3957 =
              let uu____3968 =
                let uu____3977 =
                  let uu____3978 = FStar_Syntax_Embeddings.e_option e_term
                     in
                  FStar_Syntax_Embeddings.embed uu____3978 rng md  in
                FStar_Syntax_Syntax.as_arg uu____3977  in
              [uu____3968]  in
            uu____3947 :: uu____3957  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
            uu____3946
           in
        uu____3941 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
        let uu____4016 =
          let uu____4021 =
            let uu____4022 =
              let uu____4031 = FStar_Syntax_Embeddings.embed e_term rng pre
                 in
              FStar_Syntax_Syntax.as_arg uu____4031  in
            let uu____4032 =
              let uu____4043 =
                let uu____4052 =
                  FStar_Syntax_Embeddings.embed e_term rng post1  in
                FStar_Syntax_Syntax.as_arg uu____4052  in
              [uu____4043]  in
            uu____4022 :: uu____4032  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
            uu____4021
           in
        uu____4016 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.C_Unknown  ->
        let uu___228_4079 =
          FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___228_4079.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___228_4079.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_comp_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4096 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4096 with
    | (hd1,args) ->
        let uu____4141 =
          let uu____4154 =
            let uu____4155 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4155.FStar_Syntax_Syntax.n  in
          (uu____4154, args)  in
        (match uu____4141 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____4170)::(md,uu____4172)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____4207 = FStar_Syntax_Embeddings.unembed' w e_term t2
                in
             FStar_Util.bind_opt uu____4207
               (fun t3  ->
                  let uu____4213 =
                    let uu____4218 = FStar_Syntax_Embeddings.e_option e_term
                       in
                    FStar_Syntax_Embeddings.unembed' w uu____4218 md  in
                  FStar_Util.bind_opt uu____4213
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____4237)::(post,uu____4239)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____4274 = FStar_Syntax_Embeddings.unembed' w e_term pre
                in
             FStar_Util.bind_opt uu____4274
               (fun pre1  ->
                  let uu____4280 =
                    FStar_Syntax_Embeddings.unembed' w e_term post  in
                  FStar_Util.bind_opt uu____4280
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
         | uu____4304 ->
             (if w
              then
                (let uu____4318 =
                   let uu____4323 =
                     let uu____4324 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded comp_view: %s"
                       uu____4324
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4323)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4318)
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
    let uu___229_4344 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___229_4344.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___229_4344.FStar_Syntax_Syntax.vars)
    }  in
  let unembed_order w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____4363 = FStar_Syntax_Util.head_and_args t1  in
    match uu____4363 with
    | (hd1,args) ->
        let uu____4408 =
          let uu____4423 =
            let uu____4424 = FStar_Syntax_Util.un_uinst hd1  in
            uu____4424.FStar_Syntax_Syntax.n  in
          (uu____4423, args)  in
        (match uu____4408 with
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
         | uu____4496 ->
             (if w
              then
                (let uu____4512 =
                   let uu____4517 =
                     let uu____4518 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded order: %s"
                       uu____4518
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____4517)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4512)
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
    let uu____4548 =
      let uu____4549 = FStar_Syntax_Subst.compress t  in
      uu____4549.FStar_Syntax_Syntax.n  in
    match uu____4548 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____4555 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____4555
    | uu____4556 ->
        (if w
         then
           (let uu____4558 =
              let uu____4563 =
                let uu____4564 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded sigelt: %s" uu____4564
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____4563)  in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____4558)
         else ();
         FStar_Pervasives_Native.None)
     in
  FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_Data.fstar_refl_sigelt
  
let (e_ident : FStar_Ident.ident FStar_Syntax_Embeddings.embedding) =
  let repr =
    FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_range
      FStar_Syntax_Embeddings.e_string
     in
  let embed_ident rng i =
    let uu____4588 =
      let uu____4593 = FStar_Ident.range_of_id i  in
      let uu____4594 = FStar_Ident.text_of_id i  in (uu____4593, uu____4594)
       in
    FStar_Syntax_Embeddings.embed repr rng uu____4588  in
  let unembed_ident w t =
    let uu____4614 = FStar_Syntax_Embeddings.unembed' w repr t  in
    match uu____4614 with
    | FStar_Pervasives_Native.Some (rng,s) ->
        let uu____4633 = FStar_Ident.mk_ident (s, rng)  in
        FStar_Pervasives_Native.Some uu____4633
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
  let uu____4638 =
    FStar_Syntax_Syntax.t_tuple2_of FStar_Syntax_Syntax.t_range
      FStar_Syntax_Syntax.t_string
     in
  FStar_Syntax_Embeddings.mk_emb embed_ident unembed_ident uu____4638 
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
        let uu____4667 =
          let uu____4672 =
            let uu____4673 =
              let uu____4682 =
                FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool
                  rng r
                 in
              FStar_Syntax_Syntax.as_arg uu____4682  in
            let uu____4683 =
              let uu____4694 =
                let uu____4703 = FStar_Syntax_Embeddings.embed e_fv rng fv
                   in
                FStar_Syntax_Syntax.as_arg uu____4703  in
              let uu____4704 =
                let uu____4715 =
                  let uu____4724 =
                    FStar_Syntax_Embeddings.embed e_univ_names rng univs1  in
                  FStar_Syntax_Syntax.as_arg uu____4724  in
                let uu____4727 =
                  let uu____4738 =
                    let uu____4747 =
                      FStar_Syntax_Embeddings.embed e_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____4747  in
                  let uu____4748 =
                    let uu____4759 =
                      let uu____4768 =
                        FStar_Syntax_Embeddings.embed e_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____4768  in
                    [uu____4759]  in
                  uu____4738 :: uu____4748  in
                uu____4715 :: uu____4727  in
              uu____4694 :: uu____4704  in
            uu____4673 :: uu____4683  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
            uu____4672
           in
        uu____4667 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
        let uu____4821 =
          let uu____4826 =
            let uu____4827 =
              let uu____4836 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4836  in
            let uu____4839 =
              let uu____4850 =
                let uu____4859 = FStar_Syntax_Embeddings.embed e_term rng ty
                   in
                FStar_Syntax_Syntax.as_arg uu____4859  in
              [uu____4850]  in
            uu____4827 :: uu____4839  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
            uu____4826
           in
        uu____4821 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Sg_Inductive (nm,univs1,bs,t,dcs) ->
        let uu____4903 =
          let uu____4908 =
            let uu____4909 =
              let uu____4918 =
                FStar_Syntax_Embeddings.embed
                  FStar_Syntax_Embeddings.e_string_list rng nm
                 in
              FStar_Syntax_Syntax.as_arg uu____4918  in
            let uu____4921 =
              let uu____4932 =
                let uu____4941 =
                  FStar_Syntax_Embeddings.embed e_univ_names rng univs1  in
                FStar_Syntax_Syntax.as_arg uu____4941  in
              let uu____4944 =
                let uu____4955 =
                  let uu____4964 =
                    FStar_Syntax_Embeddings.embed e_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____4964  in
                let uu____4965 =
                  let uu____4976 =
                    let uu____4985 =
                      FStar_Syntax_Embeddings.embed e_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____4985  in
                  let uu____4986 =
                    let uu____4997 =
                      let uu____5006 =
                        let uu____5007 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string_list
                           in
                        FStar_Syntax_Embeddings.embed uu____5007 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____5006  in
                    [uu____4997]  in
                  uu____4976 :: uu____4986  in
                uu____4955 :: uu____4965  in
              uu____4932 :: uu____4944  in
            uu____4909 :: uu____4921  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
            uu____4908
           in
        uu____4903 FStar_Pervasives_Native.None rng
    | FStar_Reflection_Data.Unk  ->
        let uu___230_5070 =
          FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
        {
          FStar_Syntax_Syntax.n = (uu___230_5070.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___230_5070.FStar_Syntax_Syntax.vars)
        }
     in
  let unembed_sigelt_view w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5087 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5087 with
    | (hd1,args) ->
        let uu____5132 =
          let uu____5145 =
            let uu____5146 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5146.FStar_Syntax_Syntax.n  in
          (uu____5145, args)  in
        (match uu____5132 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____5161)::(us,uu____5163)::(bs,uu____5165)::(t2,uu____5167)::
            (dcs,uu____5169)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____5234 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_string_list nm
                in
             FStar_Util.bind_opt uu____5234
               (fun nm1  ->
                  let uu____5248 =
                    FStar_Syntax_Embeddings.unembed' w e_univ_names us  in
                  FStar_Util.bind_opt uu____5248
                    (fun us1  ->
                       let uu____5262 =
                         FStar_Syntax_Embeddings.unembed' w e_binders bs  in
                       FStar_Util.bind_opt uu____5262
                         (fun bs1  ->
                            let uu____5268 =
                              FStar_Syntax_Embeddings.unembed' w e_term t2
                               in
                            FStar_Util.bind_opt uu____5268
                              (fun t3  ->
                                 let uu____5274 =
                                   let uu____5281 =
                                     FStar_Syntax_Embeddings.e_list
                                       FStar_Syntax_Embeddings.e_string_list
                                      in
                                   FStar_Syntax_Embeddings.unembed' w
                                     uu____5281 dcs
                                    in
                                 FStar_Util.bind_opt uu____5274
                                   (fun dcs1  ->
                                      FStar_All.pipe_left
                                        (fun _0_42  ->
                                           FStar_Pervasives_Native.Some _0_42)
                                        (FStar_Reflection_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____5314)::(fvar1,uu____5316)::(univs1,uu____5318)::
            (ty,uu____5320)::(t2,uu____5322)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____5387 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_bool r
                in
             FStar_Util.bind_opt uu____5387
               (fun r1  ->
                  let uu____5393 =
                    FStar_Syntax_Embeddings.unembed' w e_fv fvar1  in
                  FStar_Util.bind_opt uu____5393
                    (fun fvar2  ->
                       let uu____5399 =
                         FStar_Syntax_Embeddings.unembed' w e_univ_names
                           univs1
                          in
                       FStar_Util.bind_opt uu____5399
                         (fun univs2  ->
                            let uu____5413 =
                              FStar_Syntax_Embeddings.unembed' w e_term ty
                               in
                            FStar_Util.bind_opt uu____5413
                              (fun ty1  ->
                                 let uu____5419 =
                                   FStar_Syntax_Embeddings.unembed' w e_term
                                     t2
                                    in
                                 FStar_Util.bind_opt uu____5419
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
         | uu____5443 ->
             (if w
              then
                (let uu____5457 =
                   let uu____5462 =
                     let uu____5463 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded sigelt_view: %s"
                       uu____5463
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5462)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5457)
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
          let uu____5484 =
            let uu____5489 =
              let uu____5490 =
                let uu____5499 =
                  let uu____5500 = FStar_BigInt.string_of_big_int i  in
                  FStar_Syntax_Util.exp_int uu____5500  in
                FStar_Syntax_Syntax.as_arg uu____5499  in
              [uu____5490]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t
              uu____5489
             in
          uu____5484 FStar_Pervasives_Native.None FStar_Range.dummyRange
      | FStar_Reflection_Data.Mult (e1,e2) ->
          let uu____5521 =
            let uu____5526 =
              let uu____5527 =
                let uu____5536 = embed_exp rng e1  in
                FStar_Syntax_Syntax.as_arg uu____5536  in
              let uu____5537 =
                let uu____5548 =
                  let uu____5557 = embed_exp rng e2  in
                  FStar_Syntax_Syntax.as_arg uu____5557  in
                [uu____5548]  in
              uu____5527 :: uu____5537  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t
              uu____5526
             in
          uu____5521 FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    let uu___231_5584 = r  in
    {
      FStar_Syntax_Syntax.n = (uu___231_5584.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___231_5584.FStar_Syntax_Syntax.vars)
    }  in
  let rec unembed_exp w t =
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____5603 = FStar_Syntax_Util.head_and_args t1  in
    match uu____5603 with
    | (hd1,args) ->
        let uu____5648 =
          let uu____5661 =
            let uu____5662 = FStar_Syntax_Util.un_uinst hd1  in
            uu____5662.FStar_Syntax_Syntax.n  in
          (uu____5661, args)  in
        (match uu____5648 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____5692)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid
             ->
             let uu____5717 =
               FStar_Syntax_Embeddings.unembed' w
                 FStar_Syntax_Embeddings.e_int i
                in
             FStar_Util.bind_opt uu____5717
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Var i1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(e1,uu____5726)::(e2,uu____5728)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid
             ->
             let uu____5763 = unembed_exp w e1  in
             FStar_Util.bind_opt uu____5763
               (fun e11  ->
                  let uu____5769 = unembed_exp w e2  in
                  FStar_Util.bind_opt uu____5769
                    (fun e21  ->
                       FStar_All.pipe_left
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                         (FStar_Reflection_Data.Mult (e11, e21))))
         | uu____5776 ->
             (if w
              then
                (let uu____5790 =
                   let uu____5795 =
                     let uu____5796 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not an embedded exp: %s" uu____5796
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____5795)  in
                 FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____5790)
              else ();
              FStar_Pervasives_Native.None))
     in
  FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp
    FStar_Reflection_Data.fstar_refl_exp
  
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
    let uu____5812 =
      let uu____5817 =
        let uu____5818 =
          let uu____5827 =
            let uu____5828 = FStar_Reflection_Basic.inspect_bv bv  in
            FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng
              uu____5828
             in
          FStar_Syntax_Syntax.as_arg uu____5827  in
        [uu____5818]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t
        uu____5817
       in
    uu____5812 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let binder = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5853 = FStar_Reflection_Basic.inspect_binder binder  in
    match uu____5853 with
    | (bv,aq) ->
        let uu____5860 =
          let uu____5865 =
            let uu____5866 =
              let uu____5875 =
                FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng
                  bv
                 in
              FStar_Syntax_Syntax.as_arg uu____5875  in
            let uu____5876 =
              let uu____5887 =
                let uu____5896 =
                  FStar_Syntax_Embeddings.embed e_aqualv
                    i.FStar_Syntax_Syntax.rng aq
                   in
                FStar_Syntax_Syntax.as_arg uu____5896  in
              [uu____5887]  in
            uu____5866 :: uu____5876  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t
            uu____5865
           in
        uu____5860 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5929 =
      let uu____5934 =
        let uu____5935 =
          let uu____5944 =
            let uu____5945 =
              FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string
               in
            let uu____5950 = FStar_Reflection_Basic.inspect_fv fv  in
            FStar_Syntax_Embeddings.embed uu____5945
              i.FStar_Syntax_Syntax.rng uu____5950
             in
          FStar_Syntax_Syntax.as_arg uu____5944  in
        [uu____5935]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t
        uu____5934
       in
    uu____5929 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let comp = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____5979 =
      let uu____5984 =
        let uu____5985 =
          let uu____5994 =
            let uu____5995 = FStar_Reflection_Basic.inspect_comp comp  in
            FStar_Syntax_Embeddings.embed e_comp_view
              i.FStar_Syntax_Syntax.rng uu____5995
             in
          FStar_Syntax_Syntax.as_arg uu____5994  in
        [uu____5985]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t
        uu____5984
       in
    uu____5979 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let sigelt = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____6025 =
      let uu____6030 =
        let uu____6031 =
          let uu____6040 =
            let uu____6041 = FStar_Reflection_Basic.inspect_sigelt sigelt  in
            FStar_Syntax_Embeddings.embed e_sigelt_view
              i.FStar_Syntax_Syntax.rng uu____6041
             in
          FStar_Syntax_Syntax.as_arg uu____6040  in
        [uu____6031]  in
      FStar_Syntax_Syntax.mk_Tm_app
        FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t
        uu____6030
       in
    uu____6025 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  