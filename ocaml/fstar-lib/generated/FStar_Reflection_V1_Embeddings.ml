open Prims
let (noaqs : FStar_Syntax_Syntax.antiquotations) = (Prims.int_zero, [])
let mk_emb :
  'uuuuu .
    (FStar_Compiler_Range_Type.range -> 'uuuuu -> FStar_Syntax_Syntax.term)
      ->
      (FStar_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option) ->
        FStar_Syntax_Syntax.term ->
          'uuuuu FStar_Syntax_Embeddings_Base.embedding
  =
  fun f ->
    fun g ->
      fun t ->
        let uu___ = FStar_Syntax_Embeddings_Base.term_as_fv t in
        FStar_Syntax_Embeddings_Base.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> f r x)
          (fun x -> fun _norm -> g x) uu___
let embed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        let uu___1 = FStar_Syntax_Embeddings_Base.embed uu___ x in
        uu___1 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings_Base.id_norm_cb
let unembed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      FStar_Syntax_Embeddings_Base.try_unembed uu___ x
        FStar_Syntax_Embeddings_Base.id_norm_cb
let (e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_bv
let (e_binder :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_binder
let (e_term_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Syntax_Syntax.term FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Reflection_V2_Embeddings.e_term_aq
let (e_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_term
let (e_binders :
  FStar_Syntax_Syntax.binders FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_binders
let (e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_fv
let (e_comp :
  FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_comp
let (e_universe :
  FStar_Syntax_Syntax.universe FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Reflection_V2_Embeddings.e_universe
let (e_aqualv :
  FStar_Reflection_V1_Data.aqualv FStar_Syntax_Embeddings_Base.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStar_Reflection_V1_Data.Q_Explicit ->
          FStar_Reflection_V1_Constants.ref_Q_Explicit.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Q_Implicit ->
          FStar_Reflection_V1_Constants.ref_Q_Implicit.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Q_Meta t ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_term rng t in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Q_Meta.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_aqualv t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Q_Explicit.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Q_Implicit.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Q_Implicit
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Q_Meta.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_term t2 in
             FStar_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Q_Meta t3))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_aqualv unembed_aqualv
    FStar_Reflection_V1_Constants.fstar_refl_aqualv
let (e_ident :
  FStar_Reflection_V1_Data.ident FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_string
    FStar_Syntax_Embeddings.e_range
let (e_universe_view :
  FStar_Reflection_V1_Data.universe_view
    FStar_Syntax_Embeddings_Base.embedding)
  =
  let embed_universe_view rng uv =
    match uv with
    | FStar_Reflection_V1_Data.Uv_Zero ->
        FStar_Reflection_V1_Constants.ref_Uv_Zero.FStar_Reflection_V1_Constants.t
    | FStar_Reflection_V1_Data.Uv_Succ u ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed FStar_Reflection_V2_Embeddings.e_universe rng u in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Uv_Succ.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Uv_Max us ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed
                (FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_V2_Embeddings.e_universe) rng us in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Uv_Max.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Uv_BVar n ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_int rng n in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Uv_BVar.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Uv_Name i ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_ident rng i in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Uv_Name.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Uv_Unif u ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Syntax_Util.mk_lazy u FStar_Syntax_Util.t_universe_uvar
                FStar_Syntax_Syntax.Lazy_universe_uvar
                FStar_Pervasives_Native.None in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Uv_Unif.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Uv_Unk ->
        FStar_Reflection_V1_Constants.ref_Uv_Unk.FStar_Reflection_V1_Constants.t in
  let unembed_universe_view t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_Zero.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Uv_Zero
         | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_Succ.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStar_Reflection_V2_Embeddings.e_universe u in
             FStar_Compiler_Util.bind_opt uu___3
               (fun u1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Uv_Succ u1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (us, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_Max.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStar_Syntax_Embeddings.e_list
                    FStar_Reflection_V2_Embeddings.e_universe) us in
             FStar_Compiler_Util.bind_opt uu___3
               (fun us1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Uv_Max us1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (n, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_BVar.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStar_Syntax_Embeddings.e_int n in
             FStar_Compiler_Util.bind_opt uu___3
               (fun n1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Uv_BVar n1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_Name.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_ident i in
             FStar_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Uv_Name i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_Unif.FStar_Reflection_V1_Constants.lid
             ->
             let u1 =
               FStar_Syntax_Util.unlazy_as_t
                 FStar_Syntax_Syntax.Lazy_universe_uvar u in
             FStar_Pervasives_Native.Some
               (FStar_Reflection_V1_Data.Uv_Unif u1)
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Uv_Unk.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Uv_Unk
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_universe_view unembed_universe_view
    FStar_Reflection_V1_Constants.fstar_refl_universe_view
let (e_env :
  FStar_TypeChecker_Env.env FStar_Syntax_Embeddings_Base.embedding) =
  let embed_env rng e =
    FStar_Syntax_Util.mk_lazy e FStar_Reflection_V1_Constants.fstar_refl_env
      FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng) in
  let unembed_env t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_env unembed_env FStar_Reflection_V1_Constants.fstar_refl_env
let (e_const :
  FStar_Reflection_V1_Data.vconst FStar_Syntax_Embeddings_Base.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStar_Reflection_V1_Data.C_Unit ->
          FStar_Reflection_V1_Constants.ref_C_Unit.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.C_True ->
          FStar_Reflection_V1_Constants.ref_C_True.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.C_False ->
          FStar_Reflection_V1_Constants.ref_C_False.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.C_Int i ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_BigInt.string_of_big_int i in
                FStar_Syntax_Util.exp_int uu___3 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_C_Int.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.C_String s ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_string rng s in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_C_String.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.C_Range r1 ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_range rng r1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_C_Range.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.C_Reify ->
          FStar_Reflection_V1_Constants.ref_C_Reify.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.C_Reflect ns ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_string_list rng ns in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_C_Reflect.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed_const t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Unit.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_True.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_False.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Int.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStar_Syntax_Embeddings.e_int i in
             FStar_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (s, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_String.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStar_Syntax_Embeddings.e_string s in
             FStar_Compiler_Util.bind_opt uu___3
               (fun s1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.C_String s1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (r, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Range.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStar_Syntax_Embeddings.e_range r in
             FStar_Compiler_Util.bind_opt uu___3
               (fun r1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.C_Range r1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Reify.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.C_Reify
         | (FStar_Syntax_Syntax.Tm_fvar fv, (ns, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Reflect.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStar_Syntax_Embeddings.e_string_list ns in
             FStar_Compiler_Util.bind_opt uu___3
               (fun ns1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.C_Reflect ns1))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_const unembed_const
    FStar_Reflection_V1_Constants.fstar_refl_vconst
let rec e_pattern_aq :
  'uuuuu .
    'uuuuu ->
      FStar_Reflection_V1_Data.pattern FStar_Syntax_Embeddings_Base.embedding
  =
  fun aq ->
    let rec embed_pattern rng p =
      match p with
      | FStar_Reflection_V1_Data.Pat_Constant c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Pat_Constant.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Pat_Cons (fv, us_opt, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Reflection_V2_Embeddings.e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed
                    (FStar_Syntax_Embeddings.e_option
                       (FStar_Syntax_Embeddings.e_list
                          FStar_Reflection_V2_Embeddings.e_universe)) rng
                    us_opt in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = e_pattern_aq aq in
                        FStar_Syntax_Embeddings.e_tuple2 uu___9
                          FStar_Syntax_Embeddings.e_bool in
                      FStar_Syntax_Embeddings.e_list uu___8 in
                    embed uu___7 rng ps in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Pat_Cons.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Pat_Var (bv, sort) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed (FStar_Syntax_Embeddings.e_sealed e_term) rng sort in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Pat_Var.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Pat_Dot_Term eopt ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed (FStar_Syntax_Embeddings.e_option e_term) rng eopt in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Pat_Dot_Term.FStar_Reflection_V1_Constants.t
            uu___ rng in
    let rec unembed_pattern t =
      let t1 = FStar_Syntax_Util.unascribe t in
      let uu___ = FStar_Syntax_Util.head_and_args t1 in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Util.un_uinst hd in
              uu___3.FStar_Syntax_Syntax.n in
            (uu___2, args) in
          (match uu___1 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Pat_Constant.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_const c in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun c1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Pat_Constant c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (f, uu___2)::(us_opt, uu___3)::(ps, uu___4)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Pat_Cons.FStar_Reflection_V1_Constants.lid
               ->
               let uu___5 = unembed FStar_Reflection_V2_Embeddings.e_fv f in
               FStar_Compiler_Util.bind_opt uu___5
                 (fun f1 ->
                    let uu___6 =
                      unembed
                        (FStar_Syntax_Embeddings.e_option
                           (FStar_Syntax_Embeddings.e_list
                              FStar_Reflection_V2_Embeddings.e_universe))
                        us_opt in
                    FStar_Compiler_Util.bind_opt uu___6
                      (fun us_opt1 ->
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 = e_pattern_aq aq in
                               FStar_Syntax_Embeddings.e_tuple2 uu___10
                                 FStar_Syntax_Embeddings.e_bool in
                             FStar_Syntax_Embeddings.e_list uu___9 in
                           unembed uu___8 ps in
                         FStar_Compiler_Util.bind_opt uu___7
                           (fun ps1 ->
                              FStar_Pervasives_Native.Some
                                (FStar_Reflection_V1_Data.Pat_Cons
                                   (f1, us_opt1, ps1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (bv, uu___2)::(sort, uu___3)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Pat_Var.FStar_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed e_bv bv in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun bv1 ->
                    let uu___5 =
                      unembed (FStar_Syntax_Embeddings.e_sealed e_term) sort in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun sort1 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Reflection_V1_Data.Pat_Var (bv1, sort1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (eopt, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Pat_Dot_Term.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 =
                 unembed (FStar_Syntax_Embeddings.e_option e_term) eopt in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun eopt1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Pat_Dot_Term eopt1))
           | uu___2 -> FStar_Pervasives_Native.None) in
    mk_emb embed_pattern unembed_pattern
      FStar_Reflection_V1_Constants.fstar_refl_pattern
let (e_pattern :
  FStar_Reflection_V1_Data.pattern FStar_Syntax_Embeddings_Base.embedding) =
  e_pattern_aq noaqs
let (e_branch :
  FStar_Reflection_V1_Data.branch FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_pattern e_term
let (e_argv :
  FStar_Reflection_V1_Data.argv FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Syntax_Embeddings.e_tuple2 e_term e_aqualv
let (e_args :
  FStar_Reflection_V1_Data.argv Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Syntax_Embeddings.e_list e_argv
let (e_branch_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Reflection_V1_Data.pattern * FStar_Syntax_Syntax.term)
      FStar_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let uu___ = e_pattern_aq aq in
    let uu___1 = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 uu___ uu___1
let (e_argv_aq :
  FStar_Syntax_Syntax.antiquotations ->
    (FStar_Syntax_Syntax.term * FStar_Reflection_V1_Data.aqualv)
      FStar_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let uu___ = e_term_aq aq in
    FStar_Syntax_Embeddings.e_tuple2 uu___ e_aqualv
let (e_match_returns_annotation :
  (FStar_Syntax_Syntax.binder * ((FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.comp) FStar_Pervasives.either *
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
    FStar_Pervasives_Native.option FStar_Syntax_Embeddings_Base.embedding)
  =
  FStar_Syntax_Embeddings.e_option
    (FStar_Syntax_Embeddings.e_tuple2 e_binder
       (FStar_Syntax_Embeddings.e_tuple3
          (FStar_Syntax_Embeddings.e_either e_term e_comp)
          (FStar_Syntax_Embeddings.e_option e_term)
          FStar_Syntax_Embeddings.e_bool))
let (e_term_view_aq :
  FStar_Syntax_Syntax.antiquotations ->
    FStar_Reflection_V1_Data.term_view FStar_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let push uu___ =
      match uu___ with | (s, aq1) -> ((s + Prims.int_one), aq1) in
    let embed_term_view rng t =
      match t with
      | FStar_Reflection_V1_Data.Tv_FVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Reflection_V2_Embeddings.e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_FVar.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_BVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_BVar.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Var.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Reflection_V2_Embeddings.e_fv rng fv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed
                    (FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_V2_Embeddings.e_universe) rng us in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_UInst.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_App (hd, a) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng hd in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_argv_aq aq in embed uu___5 rng a in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_App.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Abs (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStar_Reflection_V2_Embeddings.e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Abs.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStar_Reflection_V2_Embeddings.e_binder rng b in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed FStar_Reflection_V2_Embeddings.e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Arrow.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStar_Reflection_V2_Embeddings.e_universe rng u in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Type.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Refine (bv, s, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_term_aq aq in embed uu___5 rng s in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = e_term_aq (push aq) in embed uu___7 rng t1 in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Refine.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_const rng c in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Const.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Uvar (u, d) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_int rng u in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Syntax_Util.mk_lazy (u, d)
                    FStar_Syntax_Util.t_ctx_uvar_and_sust
                    FStar_Syntax_Syntax.Lazy_uvar
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Uvar.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Let (r, attrs, b, ty, t1, t2) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStar_Syntax_Embeddings.e_bool rng r in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed (FStar_Syntax_Embeddings.e_list e_term) rng attrs in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = embed e_bv rng b in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = e_term_aq aq in embed uu___9 rng ty in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = e_term_aq aq in embed uu___11 rng t1 in
                      FStar_Syntax_Syntax.as_arg uu___10 in
                    let uu___10 =
                      let uu___11 =
                        let uu___12 =
                          let uu___13 = e_term_aq (push aq) in
                          embed uu___13 rng t2 in
                        FStar_Syntax_Syntax.as_arg uu___12 in
                      [uu___11] in
                    uu___9 :: uu___10 in
                  uu___7 :: uu___8 in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Let.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Match (t1, ret_opt, brs) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng t1 in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_match_returns_annotation rng ret_opt in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_branch_aq aq in
                      FStar_Syntax_Embeddings.e_list uu___8 in
                    embed uu___7 rng brs in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_Match.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_AscribedT (e, t1, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_term_aq aq in embed uu___5 rng t1 in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu___8 in
                    embed uu___7 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      embed FStar_Syntax_Embeddings.e_bool rng use_eq in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_AscT.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStar_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed FStar_Reflection_V2_Embeddings.e_comp rng c in
                FStar_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStar_Syntax_Embeddings.e_option uu___8 in
                    embed uu___7 rng tacopt in
                  FStar_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      embed FStar_Syntax_Embeddings.e_bool rng use_eq in
                    FStar_Syntax_Syntax.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_Tv_AscC.FStar_Reflection_V1_Constants.t
            uu___ rng
      | FStar_Reflection_V1_Data.Tv_Unknown ->
          let uu___ =
            FStar_Reflection_V1_Constants.ref_Tv_Unknown.FStar_Reflection_V1_Constants.t in
          {
            FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars);
            FStar_Syntax_Syntax.hash_code =
              (uu___.FStar_Syntax_Syntax.hash_code)
          }
      | FStar_Reflection_V1_Data.Tv_Unsupp ->
          let uu___ =
            FStar_Reflection_V1_Constants.ref_Tv_Unsupp.FStar_Reflection_V1_Constants.t in
          {
            FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars);
            FStar_Syntax_Syntax.hash_code =
              (uu___.FStar_Syntax_Syntax.hash_code)
          } in
    let unembed_term_view t =
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Util.un_uinst hd in
              uu___3.FStar_Syntax_Syntax.n in
            (uu___2, args) in
          (match uu___1 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Var.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_bv b in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun b1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Tv_Var b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_BVar.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_bv b in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun b1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Tv_BVar b1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (f, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_FVar.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed FStar_Reflection_V2_Embeddings.e_fv f in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun f1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Tv_FVar f1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (f, uu___2)::(us, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_UInst.FStar_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed FStar_Reflection_V2_Embeddings.e_fv f in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun f1 ->
                    let uu___5 =
                      unembed
                        (FStar_Syntax_Embeddings.e_list
                           FStar_Reflection_V2_Embeddings.e_universe) us in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun us1 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Reflection_V1_Data.Tv_UInst (f1, us1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::(r, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_App.FStar_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed e_term l in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun l1 ->
                    let uu___5 = unembed e_argv r in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun r1 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Reflection_V1_Data.Tv_App (l1, r1))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Abs.FStar_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed FStar_Reflection_V2_Embeddings.e_binder b in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 = unembed e_term t1 in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun t2 ->
                         FStar_Pervasives_Native.Some
                           (FStar_Reflection_V1_Data.Tv_Abs (b1, t2))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Arrow.FStar_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed FStar_Reflection_V2_Embeddings.e_binder b in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 =
                      unembed FStar_Reflection_V2_Embeddings.e_comp t1 in
                    FStar_Compiler_Util.bind_opt uu___5
                      (fun c ->
                         FStar_Pervasives_Native.Some
                           (FStar_Reflection_V1_Data.Tv_Arrow (b1, c))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Type.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 =
                 unembed FStar_Reflection_V2_Embeddings.e_universe u in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun u1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Tv_Type u1))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (b, uu___2)::(sort, uu___3)::(t1, uu___4)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Refine.FStar_Reflection_V1_Constants.lid
               ->
               let uu___5 = unembed e_bv b in
               FStar_Compiler_Util.bind_opt uu___5
                 (fun b1 ->
                    let uu___6 = unembed e_term sort in
                    FStar_Compiler_Util.bind_opt uu___6
                      (fun sort1 ->
                         let uu___7 = unembed e_term t1 in
                         FStar_Compiler_Util.bind_opt uu___7
                           (fun t2 ->
                              FStar_Pervasives_Native.Some
                                (FStar_Reflection_V1_Data.Tv_Refine
                                   (b1, sort1, t2)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (c, uu___2)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Const.FStar_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_const c in
               FStar_Compiler_Util.bind_opt uu___3
                 (fun c1 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Tv_Const c1))
           | (FStar_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::(l, uu___3)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Uvar.FStar_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed FStar_Syntax_Embeddings.e_int u in
               FStar_Compiler_Util.bind_opt uu___4
                 (fun u1 ->
                    let ctx_u_s =
                      FStar_Syntax_Util.unlazy_as_t
                        FStar_Syntax_Syntax.Lazy_uvar l in
                    FStar_Pervasives_Native.Some
                      (FStar_Reflection_V1_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (r, uu___2)::(attrs, uu___3)::(b, uu___4)::(ty, uu___5)::
              (t1, uu___6)::(t2, uu___7)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Let.FStar_Reflection_V1_Constants.lid
               ->
               let uu___8 = unembed FStar_Syntax_Embeddings.e_bool r in
               FStar_Compiler_Util.bind_opt uu___8
                 (fun r1 ->
                    let uu___9 =
                      unembed (FStar_Syntax_Embeddings.e_list e_term) attrs in
                    FStar_Compiler_Util.bind_opt uu___9
                      (fun attrs1 ->
                         let uu___10 = unembed e_bv b in
                         FStar_Compiler_Util.bind_opt uu___10
                           (fun b1 ->
                              let uu___11 = unembed e_term ty in
                              FStar_Compiler_Util.bind_opt uu___11
                                (fun ty1 ->
                                   let uu___12 = unembed e_term t1 in
                                   FStar_Compiler_Util.bind_opt uu___12
                                     (fun t11 ->
                                        let uu___13 = unembed e_term t2 in
                                        FStar_Compiler_Util.bind_opt uu___13
                                          (fun t21 ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Reflection_V1_Data.Tv_Let
                                                  (r1, attrs1, b1, ty1, t11,
                                                    t21))))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (t1, uu___2)::(ret_opt, uu___3)::(brs, uu___4)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Match.FStar_Reflection_V1_Constants.lid
               ->
               let uu___5 = unembed e_term t1 in
               FStar_Compiler_Util.bind_opt uu___5
                 (fun t2 ->
                    let uu___6 = unembed e_match_returns_annotation ret_opt in
                    FStar_Compiler_Util.bind_opt uu___6
                      (fun ret_opt1 ->
                         let uu___7 =
                           unembed (FStar_Syntax_Embeddings.e_list e_branch)
                             brs in
                         FStar_Compiler_Util.bind_opt uu___7
                           (fun brs1 ->
                              FStar_Pervasives_Native.Some
                                (FStar_Reflection_V1_Data.Tv_Match
                                   (t2, ret_opt1, brs1)))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu___2)::(t1, uu___3)::(tacopt, uu___4)::(use_eq, uu___5)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_AscT.FStar_Reflection_V1_Constants.lid
               ->
               let uu___6 = unembed e_term e in
               FStar_Compiler_Util.bind_opt uu___6
                 (fun e1 ->
                    let uu___7 = unembed e_term t1 in
                    FStar_Compiler_Util.bind_opt uu___7
                      (fun t2 ->
                         let uu___8 =
                           unembed (FStar_Syntax_Embeddings.e_option e_term)
                             tacopt in
                         FStar_Compiler_Util.bind_opt uu___8
                           (fun tacopt1 ->
                              let uu___9 =
                                unembed FStar_Syntax_Embeddings.e_bool use_eq in
                              FStar_Compiler_Util.bind_opt uu___9
                                (fun use_eq1 ->
                                   FStar_Pervasives_Native.Some
                                     (FStar_Reflection_V1_Data.Tv_AscribedT
                                        (e1, t2, tacopt1, use_eq1))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              (e, uu___2)::(c, uu___3)::(tacopt, uu___4)::(use_eq, uu___5)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_AscC.FStar_Reflection_V1_Constants.lid
               ->
               let uu___6 = unembed e_term e in
               FStar_Compiler_Util.bind_opt uu___6
                 (fun e1 ->
                    let uu___7 = unembed e_comp c in
                    FStar_Compiler_Util.bind_opt uu___7
                      (fun c1 ->
                         let uu___8 =
                           unembed (FStar_Syntax_Embeddings.e_option e_term)
                             tacopt in
                         FStar_Compiler_Util.bind_opt uu___8
                           (fun tacopt1 ->
                              let uu___9 =
                                unembed FStar_Syntax_Embeddings.e_bool use_eq in
                              FStar_Compiler_Util.bind_opt uu___9
                                (fun use_eq1 ->
                                   FStar_Pervasives_Native.Some
                                     (FStar_Reflection_V1_Data.Tv_AscribedC
                                        (e1, c1, tacopt1, use_eq1))))))
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Unknown.FStar_Reflection_V1_Constants.lid
               ->
               FStar_Pervasives_Native.Some
                 FStar_Reflection_V1_Data.Tv_Unknown
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Reflection_V1_Constants.ref_Tv_Unsupp.FStar_Reflection_V1_Constants.lid
               ->
               FStar_Pervasives_Native.Some
                 FStar_Reflection_V1_Data.Tv_Unsupp
           | uu___2 -> FStar_Pervasives_Native.None) in
    mk_emb embed_term_view unembed_term_view
      FStar_Reflection_V1_Constants.fstar_refl_term_view
let (e_term_view :
  FStar_Reflection_V1_Data.term_view FStar_Syntax_Embeddings_Base.embedding)
  = e_term_view_aq noaqs
let (e_lid : FStar_Ident.lid FStar_Syntax_Embeddings_Base.embedding) =
  let embed1 rng lid =
    let uu___ = FStar_Ident.path_of_lid lid in
    embed FStar_Syntax_Embeddings.e_string_list rng uu___ in
  let unembed1 t =
    let uu___ = unembed FStar_Syntax_Embeddings.e_string_list t in
    FStar_Compiler_Util.map_opt uu___
      (fun p -> FStar_Ident.lid_of_path p t.FStar_Syntax_Syntax.pos) in
  FStar_Syntax_Embeddings_Base.mk_emb_full
    (fun x -> fun r -> fun uu___ -> fun uu___1 -> embed1 r x)
    (fun x -> fun uu___ -> unembed1 x)
    (fun uu___ -> FStar_Syntax_Syntax.t_list_of FStar_Syntax_Syntax.t_string)
    FStar_Ident.string_of_lid (fun uu___ -> FStar_Syntax_Syntax.ET_abstract)
let (e_bv_view :
  FStar_Reflection_V1_Data.bv_view FStar_Syntax_Embeddings_Base.embedding) =
  let embed_bv_view rng bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed
            (FStar_Syntax_Embeddings.e_sealed
               FStar_Syntax_Embeddings.e_string) rng
            bvv.FStar_Reflection_V1_Data.bv_ppname in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed FStar_Syntax_Embeddings.e_int rng
              bvv.FStar_Reflection_V1_Data.bv_index in
          FStar_Syntax_Syntax.as_arg uu___4 in
        [uu___3] in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.ref_Mk_bv.FStar_Reflection_V1_Constants.t
      uu___ rng in
  let unembed_bv_view t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (nm, uu___2)::(idx, uu___3)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Mk_bv.FStar_Reflection_V1_Constants.lid
             ->
             let uu___4 =
               unembed
                 (FStar_Syntax_Embeddings.e_sealed
                    FStar_Syntax_Embeddings.e_string) nm in
             FStar_Compiler_Util.bind_opt uu___4
               (fun nm1 ->
                  let uu___5 = unembed FStar_Syntax_Embeddings.e_int idx in
                  FStar_Compiler_Util.bind_opt uu___5
                    (fun idx1 ->
                       FStar_Pervasives_Native.Some
                         {
                           FStar_Reflection_V1_Data.bv_ppname = nm1;
                           FStar_Reflection_V1_Data.bv_index = idx1
                         }))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_bv_view unembed_bv_view
    FStar_Reflection_V1_Constants.fstar_refl_bv_view
let (e_attribute :
  FStar_Syntax_Syntax.attribute FStar_Syntax_Embeddings_Base.embedding) =
  e_term
let (e_attributes :
  FStar_Syntax_Syntax.attribute Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Syntax_Embeddings.e_list e_attribute
let (e_binder_view :
  FStar_Reflection_V1_Data.binder_view FStar_Syntax_Embeddings_Base.embedding)
  =
  let embed_binder_view rng bview =
    let uu___ =
      let uu___1 =
        let uu___2 = embed e_bv rng bview.FStar_Reflection_V1_Data.binder_bv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed e_aqualv rng bview.FStar_Reflection_V1_Data.binder_qual in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_attributes rng
                bview.FStar_Reflection_V1_Data.binder_attrs in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term rng bview.FStar_Reflection_V1_Data.binder_sort in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.ref_Mk_binder.FStar_Reflection_V1_Constants.t
      uu___ rng in
  let unembed_binder_view t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (bv, uu___2)::(q, uu___3)::(attrs, uu___4)::(sort, uu___5)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Mk_binder.FStar_Reflection_V1_Constants.lid
             ->
             let uu___6 = unembed e_bv bv in
             FStar_Compiler_Util.bind_opt uu___6
               (fun bv1 ->
                  let uu___7 = unembed e_aqualv q in
                  FStar_Compiler_Util.bind_opt uu___7
                    (fun q1 ->
                       let uu___8 = unembed e_attributes attrs in
                       FStar_Compiler_Util.bind_opt uu___8
                         (fun attrs1 ->
                            let uu___9 = unembed e_term sort in
                            FStar_Compiler_Util.bind_opt uu___9
                              (fun sort1 ->
                                 FStar_Pervasives_Native.Some
                                   {
                                     FStar_Reflection_V1_Data.binder_bv = bv1;
                                     FStar_Reflection_V1_Data.binder_qual =
                                       q1;
                                     FStar_Reflection_V1_Data.binder_attrs =
                                       attrs1;
                                     FStar_Reflection_V1_Data.binder_sort =
                                       sort1
                                   }))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_binder_view unembed_binder_view
    FStar_Reflection_V1_Constants.fstar_refl_binder_view
let (e_comp_view :
  FStar_Reflection_V1_Data.comp_view FStar_Syntax_Embeddings_Base.embedding)
  =
  let embed_comp_view rng cv =
    match cv with
    | FStar_Reflection_V1_Data.C_Total t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_C_Total.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.C_GTotal t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStar_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_C_GTotal.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng pre in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_term rng post in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng pats in
                FStar_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_C_Lemma.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.C_Eff (us, eff, res, args, decrs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed
                (FStar_Syntax_Embeddings.e_list
                   FStar_Reflection_V2_Embeddings.e_universe) rng us in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed FStar_Syntax_Embeddings.e_string_list rng eff in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng res in
                FStar_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    embed (FStar_Syntax_Embeddings.e_list e_argv) rng args in
                  FStar_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      embed (FStar_Syntax_Embeddings.e_list e_term) rng decrs in
                    FStar_Syntax_Syntax.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_C_Eff.FStar_Reflection_V1_Constants.t
          uu___ rng in
  let unembed_comp_view t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Total.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_term t2 in
             FStar_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.C_Total t3))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_GTotal.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_term t2 in
             FStar_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.C_GTotal t3))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (pre, uu___2)::(post, uu___3)::(pats, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Lemma.FStar_Reflection_V1_Constants.lid
             ->
             let uu___5 = unembed e_term pre in
             FStar_Compiler_Util.bind_opt uu___5
               (fun pre1 ->
                  let uu___6 = unembed e_term post in
                  FStar_Compiler_Util.bind_opt uu___6
                    (fun post1 ->
                       let uu___7 = unembed e_term pats in
                       FStar_Compiler_Util.bind_opt uu___7
                         (fun pats1 ->
                            FStar_Pervasives_Native.Some
                              (FStar_Reflection_V1_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (us, uu___2)::(eff, uu___3)::(res, uu___4)::(args1, uu___5)::
            (decrs, uu___6)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_C_Eff.FStar_Reflection_V1_Constants.lid
             ->
             let uu___7 =
               unembed
                 (FStar_Syntax_Embeddings.e_list
                    FStar_Reflection_V2_Embeddings.e_universe) us in
             FStar_Compiler_Util.bind_opt uu___7
               (fun us1 ->
                  let uu___8 =
                    unembed FStar_Syntax_Embeddings.e_string_list eff in
                  FStar_Compiler_Util.bind_opt uu___8
                    (fun eff1 ->
                       let uu___9 = unembed e_term res in
                       FStar_Compiler_Util.bind_opt uu___9
                         (fun res1 ->
                            let uu___10 =
                              unembed (FStar_Syntax_Embeddings.e_list e_argv)
                                args1 in
                            FStar_Compiler_Util.bind_opt uu___10
                              (fun args2 ->
                                 let uu___11 =
                                   unembed
                                     (FStar_Syntax_Embeddings.e_list e_term)
                                     decrs in
                                 FStar_Compiler_Util.bind_opt uu___11
                                   (fun decrs1 ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Reflection_V1_Data.C_Eff
                                           (us1, eff1, res1, args2, decrs1)))))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_comp_view unembed_comp_view
    FStar_Reflection_V1_Constants.fstar_refl_comp_view
let (e_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings_Base.embedding) =
  let embed_sigelt rng se =
    FStar_Syntax_Util.mk_lazy se
      FStar_Reflection_V1_Constants.fstar_refl_sigelt
      FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng) in
  let unembed_sigelt t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = b;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_sigelt unembed_sigelt
    FStar_Reflection_V1_Constants.fstar_refl_sigelt
let (e_univ_name :
  FStar_Reflection_V1_Data.univ_name FStar_Syntax_Embeddings_Base.embedding)
  =
  FStar_Syntax_Embeddings_Base.set_type
    FStar_Reflection_V1_Constants.fstar_refl_univ_name e_ident
let (e_lb_view :
  FStar_Reflection_V1_Data.lb_view FStar_Syntax_Embeddings_Base.embedding) =
  let embed_lb_view rng lbv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStar_Reflection_V2_Embeddings.e_fv rng
            lbv.FStar_Reflection_V1_Data.lb_fv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed (FStar_Syntax_Embeddings.e_list e_ident) rng
              lbv.FStar_Reflection_V1_Data.lb_us in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 = embed e_term rng lbv.FStar_Reflection_V1_Data.lb_typ in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term rng lbv.FStar_Reflection_V1_Data.lb_def in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.ref_Mk_lb.FStar_Reflection_V1_Constants.t
      uu___ rng in
  let unembed_lb_view t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (fv', uu___2)::(us, uu___3)::(typ, uu___4)::(def, uu___5)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Mk_lb.FStar_Reflection_V1_Constants.lid
             ->
             let uu___6 = unembed FStar_Reflection_V2_Embeddings.e_fv fv' in
             FStar_Compiler_Util.bind_opt uu___6
               (fun fv'1 ->
                  let uu___7 =
                    unembed (FStar_Syntax_Embeddings.e_list e_ident) us in
                  FStar_Compiler_Util.bind_opt uu___7
                    (fun us1 ->
                       let uu___8 = unembed e_term typ in
                       FStar_Compiler_Util.bind_opt uu___8
                         (fun typ1 ->
                            let uu___9 = unembed e_term def in
                            FStar_Compiler_Util.bind_opt uu___9
                              (fun def1 ->
                                 FStar_Pervasives_Native.Some
                                   {
                                     FStar_Reflection_V1_Data.lb_fv = fv'1;
                                     FStar_Reflection_V1_Data.lb_us = us1;
                                     FStar_Reflection_V1_Data.lb_typ = typ1;
                                     FStar_Reflection_V1_Data.lb_def = def1
                                   }))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_lb_view unembed_lb_view
    FStar_Reflection_V1_Constants.fstar_refl_lb_view
let (e_letbinding :
  FStar_Syntax_Syntax.letbinding FStar_Syntax_Embeddings_Base.embedding) =
  let embed_letbinding rng lb =
    FStar_Syntax_Util.mk_lazy lb
      FStar_Reflection_V1_Constants.fstar_refl_letbinding
      FStar_Syntax_Syntax.Lazy_letbinding (FStar_Pervasives_Native.Some rng) in
  let unembed_letbinding t =
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_lazy
        { FStar_Syntax_Syntax.blob = lb;
          FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_letbinding;
          FStar_Syntax_Syntax.ltyp = uu___1;
          FStar_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStar_Compiler_Dyn.undyn lb in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_letbinding unembed_letbinding
    FStar_Reflection_V1_Constants.fstar_refl_letbinding
let (e_ctor :
  FStar_Reflection_V1_Data.ctor FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Syntax_Embeddings.e_tuple2
    (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string) e_term
let (e_sigelt_view :
  FStar_Reflection_V1_Data.sigelt_view FStar_Syntax_Embeddings_Base.embedding)
  =
  let embed_sigelt_view rng sev =
    match sev with
    | FStar_Reflection_V1_Data.Sg_Let (r, lbs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_bool rng r in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed
                  (FStar_Syntax_Embeddings.e_list
                     FStar_Reflection_V2_Embeddings.e_letbinding) rng lbs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Sg_Let.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStar_Syntax_Embeddings.e_list e_ident) rng univs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  embed FStar_Reflection_V2_Embeddings.e_binders rng bs in
                FStar_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 = embed e_term rng t in
                  FStar_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      embed (FStar_Syntax_Embeddings.e_list e_ctor) rng dcs in
                    FStar_Syntax_Syntax.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Sg_Inductive.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Sg_Val (nm, univs, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStar_Syntax_Embeddings.e_string_list rng nm in
            FStar_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStar_Syntax_Embeddings.e_list e_ident) rng univs in
              FStar_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng t in
                FStar_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_V1_Constants.ref_Sg_Val.FStar_Reflection_V1_Constants.t
          uu___ rng
    | FStar_Reflection_V1_Data.Unk ->
        let uu___ =
          FStar_Reflection_V1_Constants.ref_Unk.FStar_Reflection_V1_Constants.t in
        {
          FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = rng;
          FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars);
          FStar_Syntax_Syntax.hash_code =
            (uu___.FStar_Syntax_Syntax.hash_code)
        } in
  let unembed_sigelt_view t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(us, uu___3)::(bs, uu___4)::(t2, uu___5)::(dcs,
                                                                    uu___6)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Sg_Inductive.FStar_Reflection_V1_Constants.lid
             ->
             let uu___7 = unembed FStar_Syntax_Embeddings.e_string_list nm in
             FStar_Compiler_Util.bind_opt uu___7
               (fun nm1 ->
                  let uu___8 =
                    unembed (FStar_Syntax_Embeddings.e_list e_ident) us in
                  FStar_Compiler_Util.bind_opt uu___8
                    (fun us1 ->
                       let uu___9 =
                         unembed FStar_Reflection_V2_Embeddings.e_binders bs in
                       FStar_Compiler_Util.bind_opt uu___9
                         (fun bs1 ->
                            let uu___10 = unembed e_term t2 in
                            FStar_Compiler_Util.bind_opt uu___10
                              (fun t3 ->
                                 let uu___11 =
                                   unembed
                                     (FStar_Syntax_Embeddings.e_list e_ctor)
                                     dcs in
                                 FStar_Compiler_Util.bind_opt uu___11
                                   (fun dcs1 ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Reflection_V1_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (r, uu___2)::(lbs, uu___3)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Sg_Let.FStar_Reflection_V1_Constants.lid
             ->
             let uu___4 = unembed FStar_Syntax_Embeddings.e_bool r in
             FStar_Compiler_Util.bind_opt uu___4
               (fun r1 ->
                  let uu___5 =
                    unembed
                      (FStar_Syntax_Embeddings.e_list
                         FStar_Reflection_V2_Embeddings.e_letbinding) lbs in
                  FStar_Compiler_Util.bind_opt uu___5
                    (fun lbs1 ->
                       FStar_Pervasives_Native.Some
                         (FStar_Reflection_V1_Data.Sg_Let (r1, lbs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(us, uu___3)::(t2, uu___4)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Sg_Val.FStar_Reflection_V1_Constants.lid
             ->
             let uu___5 = unembed FStar_Syntax_Embeddings.e_string_list nm in
             FStar_Compiler_Util.bind_opt uu___5
               (fun nm1 ->
                  let uu___6 =
                    unembed (FStar_Syntax_Embeddings.e_list e_ident) us in
                  FStar_Compiler_Util.bind_opt uu___6
                    (fun us1 ->
                       let uu___7 = unembed e_term t2 in
                       FStar_Compiler_Util.bind_opt uu___7
                         (fun t3 ->
                            FStar_Pervasives_Native.Some
                              (FStar_Reflection_V1_Data.Sg_Val (nm1, us1, t3)))))
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_Unk.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Unk
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStar_Reflection_V1_Constants.fstar_refl_sigelt_view
let (e_qualifier :
  FStar_Reflection_V1_Data.qualifier FStar_Syntax_Embeddings_Base.embedding)
  =
  let embed1 rng q =
    let r =
      match q with
      | FStar_Reflection_V1_Data.Assumption ->
          FStar_Reflection_V1_Constants.ref_qual_Assumption.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.InternalAssumption ->
          FStar_Reflection_V1_Constants.ref_qual_InternalAssumption.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.New ->
          FStar_Reflection_V1_Constants.ref_qual_New.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Private ->
          FStar_Reflection_V1_Constants.ref_qual_Private.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Unfold_for_unification_and_vcgen ->
          FStar_Reflection_V1_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Visible_default ->
          FStar_Reflection_V1_Constants.ref_qual_Visible_default.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Irreducible ->
          FStar_Reflection_V1_Constants.ref_qual_Irreducible.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Inline_for_extraction ->
          FStar_Reflection_V1_Constants.ref_qual_Inline_for_extraction.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.NoExtract ->
          FStar_Reflection_V1_Constants.ref_qual_NoExtract.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Noeq ->
          FStar_Reflection_V1_Constants.ref_qual_Noeq.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Unopteq ->
          FStar_Reflection_V1_Constants.ref_qual_Unopteq.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.TotalEffect ->
          FStar_Reflection_V1_Constants.ref_qual_TotalEffect.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Logic ->
          FStar_Reflection_V1_Constants.ref_qual_Logic.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Reifiable ->
          FStar_Reflection_V1_Constants.ref_qual_Reifiable.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.ExceptionConstructor ->
          FStar_Reflection_V1_Constants.ref_qual_ExceptionConstructor.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.HasMaskedEffect ->
          FStar_Reflection_V1_Constants.ref_qual_HasMaskedEffect.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Effect ->
          FStar_Reflection_V1_Constants.ref_qual_Effect.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.OnlyName ->
          FStar_Reflection_V1_Constants.ref_qual_OnlyName.FStar_Reflection_V1_Constants.t
      | FStar_Reflection_V1_Data.Reflectable l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_qual_Reflectable.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.Discriminator l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_qual_Discriminator.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.Action l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_lid rng l in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_qual_Action.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.Projector (l, i) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed (FStar_Syntax_Embeddings.e_tuple2 e_lid e_ident) rng
                  (l, i) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_qual_Projector.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.RecordType (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStar_Syntax_Embeddings.e_tuple2
                     (FStar_Syntax_Embeddings.e_list e_ident)
                     (FStar_Syntax_Embeddings.e_list e_ident)) rng
                  (ids1, ids2) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_qual_RecordType.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange
      | FStar_Reflection_V1_Data.RecordConstructor (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStar_Syntax_Embeddings.e_tuple2
                     (FStar_Syntax_Embeddings.e_list e_ident)
                     (FStar_Syntax_Embeddings.e_list e_ident)) rng
                  (ids1, ids2) in
              FStar_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_V1_Constants.ref_qual_RecordConstructor.FStar_Reflection_V1_Constants.t
            uu___ FStar_Compiler_Range_Type.dummyRange in
    {
      FStar_Syntax_Syntax.n = (r.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (r.FStar_Syntax_Syntax.vars);
      FStar_Syntax_Syntax.hash_code = (r.FStar_Syntax_Syntax.hash_code)
    } in
  let unembed1 t =
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Assumption.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Assumption
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_InternalAssumption.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.InternalAssumption
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_New.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.New
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Private.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Private
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.Unfold_for_unification_and_vcgen
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Visible_default.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.Visible_default
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Irreducible.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.Irreducible
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Inline_for_extraction.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.Inline_for_extraction
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_NoExtract.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.NoExtract
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Noeq.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Noeq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Unopteq.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Unopteq
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_TotalEffect.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.TotalEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Logic.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Logic
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Reifiable.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Reifiable
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_ExceptionConstructor.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.ExceptionConstructor
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_HasMaskedEffect.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStar_Reflection_V1_Data.HasMaskedEffect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Effect.FStar_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.Effect
         | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_OnlyName.FStar_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStar_Reflection_V1_Data.OnlyName
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Reflectable.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_lid l in
             FStar_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Reflectable l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Discriminator.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_lid l in
             FStar_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Discriminator l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Action.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_lid l in
             FStar_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Reflection_V1_Data.Action l1))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_Projector.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed (FStar_Syntax_Embeddings.e_tuple2 e_lid e_ident)
                 payload in
             FStar_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (l, i) ->
                      FStar_Pervasives_Native.Some
                        (FStar_Reflection_V1_Data.Projector (l, i)))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_RecordType.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStar_Syntax_Embeddings.e_tuple2
                    (FStar_Syntax_Embeddings.e_list e_ident)
                    (FStar_Syntax_Embeddings.e_list e_ident)) payload in
             FStar_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (ids1, ids2) ->
                      FStar_Pervasives_Native.Some
                        (FStar_Reflection_V1_Data.RecordType (ids1, ids2)))
         | (FStar_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_V1_Constants.ref_qual_RecordConstructor.FStar_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStar_Syntax_Embeddings.e_tuple2
                    (FStar_Syntax_Embeddings.e_list e_ident)
                    (FStar_Syntax_Embeddings.e_list e_ident)) payload in
             FStar_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (ids1, ids2) ->
                      FStar_Pervasives_Native.Some
                        (FStar_Reflection_V1_Data.RecordConstructor
                           (ids1, ids2)))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed1 unembed1 FStar_Reflection_V1_Constants.fstar_refl_qualifier
let (e_qualifiers :
  FStar_Reflection_V1_Data.qualifier Prims.list
    FStar_Syntax_Embeddings_Base.embedding)
  = FStar_Syntax_Embeddings.e_list e_qualifier
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let bv = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_V1_Builtins.inspect_bv bv in
          embed e_bv_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_bv.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let binder = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_V1_Builtins.inspect_binder binder in
          embed e_binder_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_binder.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_letbinding :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let lb = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let lbv = FStar_Reflection_V1_Builtins.inspect_lb lb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStar_Reflection_V2_Embeddings.e_fv i.FStar_Syntax_Syntax.rng
            lbv.FStar_Reflection_V1_Data.lb_fv in
        FStar_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed (FStar_Syntax_Embeddings.e_list e_ident)
              i.FStar_Syntax_Syntax.rng lbv.FStar_Reflection_V1_Data.lb_us in
          FStar_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_term i.FStar_Syntax_Syntax.rng
                lbv.FStar_Reflection_V1_Data.lb_typ in
            FStar_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term i.FStar_Syntax_Syntax.rng
                  lbv.FStar_Reflection_V1_Data.lb_def in
              FStar_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_lb.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let fv = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_V1_Builtins.inspect_fv fv in
          embed FStar_Syntax_Embeddings.e_string_list
            i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_fv.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let comp = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_V1_Builtins.inspect_comp comp in
          embed e_comp_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_comp.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_unit
let (unfold_lazy_optionstate :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i -> FStar_Syntax_Util.exp_unit
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let sigelt = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_V1_Builtins.inspect_sigelt sigelt in
          embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_sigelt.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng
let (unfold_lazy_universe :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i ->
    let u = FStar_Compiler_Dyn.undyn i.FStar_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Reflection_V1_Builtins.inspect_universe u in
          embed e_universe_view i.FStar_Syntax_Syntax.rng uu___3 in
        FStar_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app
      FStar_Reflection_V1_Constants.fstar_refl_pack_universe.FStar_Reflection_V1_Constants.t
      uu___ i.FStar_Syntax_Syntax.rng