open Prims
let (noaqs : FStarC_Syntax_Syntax.antiquotations) = (Prims.int_zero, [])
let mk_emb :
  'uuuuu .
    (FStarC_Compiler_Range_Type.range -> 'uuuuu -> FStarC_Syntax_Syntax.term)
      ->
      (FStarC_Syntax_Syntax.term -> 'uuuuu FStar_Pervasives_Native.option) ->
        FStarC_Syntax_Syntax.term ->
          'uuuuu FStarC_Syntax_Embeddings_Base.embedding
  =
  fun f ->
    fun g ->
      fun t ->
        let uu___ = FStarC_Syntax_Embeddings_Base.term_as_fv t in
        FStarC_Syntax_Embeddings_Base.mk_emb
          (fun x -> fun r -> fun _topt -> fun _norm -> f r x)
          (fun x -> fun _norm -> g x) uu___
let embed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Compiler_Range_Type.range -> 'a -> FStarC_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        let uu___1 = FStarC_Syntax_Embeddings_Base.embed uu___ x in
        uu___1 r FStar_Pervasives_Native.None
          FStarC_Syntax_Embeddings_Base.id_norm_cb
let unembed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      FStarC_Syntax_Embeddings_Base.try_unembed uu___ x
        FStarC_Syntax_Embeddings_Base.id_norm_cb
let (e_bv : FStarC_Syntax_Syntax.bv FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Reflection_V2_Embeddings.e_bv
let (e_binder :
  FStarC_Syntax_Syntax.binder FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_binder
let (e_term_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Reflection_V2_Embeddings.e_term_aq
let (e_term :
  FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_term
let (e_binders :
  FStarC_Syntax_Syntax.binders FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_binders
let (e_fv : FStarC_Syntax_Syntax.fv FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Reflection_V2_Embeddings.e_fv
let (e_comp :
  FStarC_Syntax_Syntax.comp FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_comp
let (e_universe :
  FStarC_Syntax_Syntax.universe FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_universe
let (e_aqualv :
  FStarC_Reflection_V1_Data.aqualv FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStarC_Reflection_V1_Data.Q_Explicit ->
          FStarC_Reflection_V1_Constants.ref_Q_Explicit.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Q_Implicit ->
          FStarC_Reflection_V1_Constants.ref_Q_Implicit.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Q_Meta t ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_term rng t in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Q_Meta.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed_aqualv t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Q_Explicit.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Q_Explicit
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Q_Implicit.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Q_Implicit
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Q_Meta.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_term t2 in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Q_Meta t3))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_aqualv unembed_aqualv
    FStarC_Reflection_V1_Constants.fstar_refl_aqualv
let (e_ident :
  FStarC_Reflection_V1_Data.ident FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_tuple2 FStarC_Syntax_Embeddings.e_string
    FStarC_Syntax_Embeddings.e_range
let (e_universe_view :
  FStarC_Reflection_V1_Data.universe_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_universe_view rng uv =
    match uv with
    | FStarC_Reflection_V1_Data.Uv_Zero ->
        FStarC_Reflection_V1_Constants.ref_Uv_Zero.FStarC_Reflection_V1_Constants.t
    | FStarC_Reflection_V1_Data.Uv_Succ u ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed FStarC_Reflection_V2_Embeddings.e_universe rng u in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Uv_Succ.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Uv_Max us ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Reflection_V2_Embeddings.e_universe) rng us in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Uv_Max.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Uv_BVar n ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_int rng n in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Uv_BVar.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Uv_Name i ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_ident rng i in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Uv_Name.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Uv_Unif u ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Util.mk_lazy u FStarC_Syntax_Util.t_universe_uvar
                FStarC_Syntax_Syntax.Lazy_universe_uvar
                FStar_Pervasives_Native.None in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Uv_Unif.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Uv_Unk ->
        FStarC_Reflection_V1_Constants.ref_Uv_Unk.FStarC_Reflection_V1_Constants.t in
  let unembed_universe_view t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_Zero.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Uv_Zero
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_Succ.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed FStarC_Reflection_V2_Embeddings.e_universe u in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun u1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Uv_Succ u1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (us, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_Max.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStarC_Syntax_Embeddings.e_list
                    FStarC_Reflection_V2_Embeddings.e_universe) us in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun us1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Uv_Max us1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (n, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_BVar.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_int n in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun n1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Uv_BVar n1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_Name.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_ident i in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Uv_Name i1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_Unif.FStarC_Reflection_V1_Constants.lid
             ->
             let u1 =
               FStarC_Syntax_Util.unlazy_as_t
                 FStarC_Syntax_Syntax.Lazy_universe_uvar u in
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V1_Data.Uv_Unif u1)
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Uv_Unk.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Uv_Unk
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_universe_view unembed_universe_view
    FStarC_Reflection_V1_Constants.fstar_refl_universe_view
let (e_env :
  FStarC_TypeChecker_Env.env FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_env rng e =
    FStarC_Syntax_Util.mk_lazy e
      FStarC_Reflection_V1_Constants.fstar_refl_env
      FStarC_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng) in
  let unembed_env t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_lazy
        { FStarC_Syntax_Syntax.blob = b;
          FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_env;
          FStarC_Syntax_Syntax.ltyp = uu___1;
          FStarC_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_env unembed_env FStarC_Reflection_V1_Constants.fstar_refl_env
let (e_const :
  FStarC_Reflection_V1_Data.vconst FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStarC_Reflection_V1_Data.C_Unit ->
          FStarC_Reflection_V1_Constants.ref_C_Unit.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.C_True ->
          FStarC_Reflection_V1_Constants.ref_C_True.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.C_False ->
          FStarC_Reflection_V1_Constants.ref_C_False.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.C_Int i ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_BigInt.string_of_big_int i in
                FStarC_Syntax_Util.exp_int uu___3 in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_C_Int.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.C_String s ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string rng s in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_C_String.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.C_Range r1 ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_range rng r1 in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_C_Range.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.C_Reify ->
          FStarC_Reflection_V1_Constants.ref_C_Reify.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.C_Reflect ns ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStarC_Syntax_Embeddings.e_string_list rng ns in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_C_Reflect.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed_const t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Unit.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.C_Unit
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_True.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.C_True
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_False.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.C_False
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (i, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Int.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_int i in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.C_Int i1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (s, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_String.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_string s in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun s1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.C_String s1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (r, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Range.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_range r in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun r1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.C_Range r1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Reify.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.C_Reify
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (ns, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Reflect.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_string_list ns in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun ns1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.C_Reflect ns1))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_const unembed_const
    FStarC_Reflection_V1_Constants.fstar_refl_vconst
let rec e_pattern_aq :
  'uuuuu .
    'uuuuu ->
      FStarC_Reflection_V1_Data.pattern
        FStarC_Syntax_Embeddings_Base.embedding
  =
  fun aq ->
    let rec embed_pattern rng p =
      match p with
      | FStarC_Reflection_V1_Data.Pat_Constant c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_const rng c in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Pat_Constant.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Pat_Cons (fv, us_opt, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Reflection_V2_Embeddings.e_fv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed
                    (FStarC_Syntax_Embeddings.e_option
                       (FStarC_Syntax_Embeddings.e_list
                          FStarC_Reflection_V2_Embeddings.e_universe)) rng
                    us_opt in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = e_pattern_aq aq in
                        FStarC_Syntax_Embeddings.e_tuple2 uu___9
                          FStarC_Syntax_Embeddings.e_bool in
                      FStarC_Syntax_Embeddings.e_list uu___8 in
                    embed uu___7 rng ps in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Pat_Cons.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Pat_Var (bv, sort) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed (FStarC_Syntax_Embeddings.e_sealed e_term) rng sort in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Pat_Var.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Pat_Dot_Term eopt ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed (FStarC_Syntax_Embeddings.e_option e_term) rng eopt in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Pat_Dot_Term.FStarC_Reflection_V1_Constants.t
            uu___ rng in
    let rec unembed_pattern t =
      let t1 = FStarC_Syntax_Util.unascribe t in
      let uu___ = FStarC_Syntax_Util.head_and_args t1 in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Util.un_uinst hd in
              uu___3.FStarC_Syntax_Syntax.n in
            (uu___2, args) in
          (match uu___1 with
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (c, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Pat_Constant.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_const c in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun c1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Pat_Constant c1))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (f, uu___2)::(us_opt, uu___3)::(ps, uu___4)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Pat_Cons.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___5 = unembed FStarC_Reflection_V2_Embeddings.e_fv f in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun f1 ->
                    let uu___6 =
                      unembed
                        (FStarC_Syntax_Embeddings.e_option
                           (FStarC_Syntax_Embeddings.e_list
                              FStarC_Reflection_V2_Embeddings.e_universe))
                        us_opt in
                    FStarC_Compiler_Util.bind_opt uu___6
                      (fun us_opt1 ->
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 = e_pattern_aq aq in
                               FStarC_Syntax_Embeddings.e_tuple2 uu___10
                                 FStarC_Syntax_Embeddings.e_bool in
                             FStarC_Syntax_Embeddings.e_list uu___9 in
                           unembed uu___8 ps in
                         FStarC_Compiler_Util.bind_opt uu___7
                           (fun ps1 ->
                              FStar_Pervasives_Native.Some
                                (FStarC_Reflection_V1_Data.Pat_Cons
                                   (f1, us_opt1, ps1)))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (bv, uu___2)::(sort, uu___3)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Pat_Var.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed e_bv bv in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun bv1 ->
                    let uu___5 =
                      unembed (FStarC_Syntax_Embeddings.e_sealed e_term) sort in
                    FStarC_Compiler_Util.bind_opt uu___5
                      (fun sort1 ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V1_Data.Pat_Var (bv1, sort1))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (eopt, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Pat_Dot_Term.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 =
                 unembed (FStarC_Syntax_Embeddings.e_option e_term) eopt in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun eopt1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Pat_Dot_Term eopt1))
           | uu___2 -> FStar_Pervasives_Native.None) in
    mk_emb embed_pattern unembed_pattern
      FStarC_Reflection_V1_Constants.fstar_refl_pattern
let (e_pattern :
  FStarC_Reflection_V1_Data.pattern FStarC_Syntax_Embeddings_Base.embedding)
  = e_pattern_aq noaqs
let (e_branch :
  FStarC_Reflection_V1_Data.branch FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_tuple2 e_pattern e_term
let (e_argv :
  FStarC_Reflection_V1_Data.argv FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_tuple2 e_term e_aqualv
let (e_args :
  FStarC_Reflection_V1_Data.argv Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_argv
let (e_branch_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    (FStarC_Reflection_V1_Data.pattern * FStarC_Syntax_Syntax.term)
      FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let uu___ = e_pattern_aq aq in
    let uu___1 = e_term_aq aq in
    FStarC_Syntax_Embeddings.e_tuple2 uu___ uu___1
let (e_argv_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    (FStarC_Syntax_Syntax.term * FStarC_Reflection_V1_Data.aqualv)
      FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let uu___ = e_term_aq aq in
    FStarC_Syntax_Embeddings.e_tuple2 uu___ e_aqualv
let (e_match_returns_annotation :
  (FStarC_Syntax_Syntax.binder * ((FStarC_Syntax_Syntax.term,
    FStarC_Syntax_Syntax.comp) FStar_Pervasives.either *
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
    FStar_Pervasives_Native.option FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings.e_option
    (FStarC_Syntax_Embeddings.e_tuple2 e_binder
       (FStarC_Syntax_Embeddings.e_tuple3
          (FStarC_Syntax_Embeddings.e_either e_term e_comp)
          (FStarC_Syntax_Embeddings.e_option e_term)
          FStarC_Syntax_Embeddings.e_bool))
let (e_term_view_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    FStarC_Reflection_V1_Data.term_view
      FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let push uu___ =
      match uu___ with | (s, aq1) -> ((s + Prims.int_one), aq1) in
    let embed_term_view rng t =
      match t with
      | FStarC_Reflection_V1_Data.Tv_FVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Reflection_V2_Embeddings.e_fv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_FVar.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_BVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_BVar.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Var.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Reflection_V2_Embeddings.e_fv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed
                    (FStarC_Syntax_Embeddings.e_list
                       FStarC_Reflection_V2_Embeddings.e_universe) rng us in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_UInst.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_App (hd, a) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng hd in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_argv_aq aq in embed uu___5 rng a in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_App.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Abs (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStarC_Reflection_V2_Embeddings.e_binder rng b in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in embed uu___5 rng t1 in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Abs.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStarC_Reflection_V2_Embeddings.e_binder rng b in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed FStarC_Reflection_V2_Embeddings.e_comp rng c in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Arrow.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStarC_Reflection_V2_Embeddings.e_universe rng u in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Type.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Refine (bv, s, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng bv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_term_aq aq in embed uu___5 rng s in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = e_term_aq (push aq) in embed uu___7 rng t1 in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Refine.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_const rng c in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Const.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Uvar (u, d) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_int rng u in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Syntax_Util.mk_lazy (u, d)
                    FStarC_Syntax_Util.t_ctx_uvar_and_sust
                    FStarC_Syntax_Syntax.Lazy_uvar
                    FStar_Pervasives_Native.None in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Uvar.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Let (r, attrs, b, ty, t1, t2) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_bool rng r in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed (FStarC_Syntax_Embeddings.e_list e_term) rng attrs in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = embed e_bv rng b in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = e_term_aq aq in embed uu___9 rng ty in
                    FStarC_Syntax_Syntax.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = e_term_aq aq in embed uu___11 rng t1 in
                      FStarC_Syntax_Syntax.as_arg uu___10 in
                    let uu___10 =
                      let uu___11 =
                        let uu___12 =
                          let uu___13 = e_term_aq (push aq) in
                          embed uu___13 rng t2 in
                        FStarC_Syntax_Syntax.as_arg uu___12 in
                      [uu___11] in
                    uu___9 :: uu___10 in
                  uu___7 :: uu___8 in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Let.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Match (t1, ret_opt, brs) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng t1 in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_match_returns_annotation rng ret_opt in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_branch_aq aq in
                      FStarC_Syntax_Embeddings.e_list uu___8 in
                    embed uu___7 rng brs in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_Match.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_AscribedT (e, t1, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = let uu___5 = e_term_aq aq in embed uu___5 rng t1 in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStarC_Syntax_Embeddings.e_option uu___8 in
                    embed uu___7 rng tacopt in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      embed FStarC_Syntax_Embeddings.e_bool rng use_eq in
                    FStarC_Syntax_Syntax.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_AscT.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed FStarC_Reflection_V2_Embeddings.e_comp rng c in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_term_aq aq in
                      FStarC_Syntax_Embeddings.e_option uu___8 in
                    embed uu___7 rng tacopt in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      embed FStarC_Syntax_Embeddings.e_bool rng use_eq in
                    FStarC_Syntax_Syntax.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_Tv_AscC.FStarC_Reflection_V1_Constants.t
            uu___ rng
      | FStarC_Reflection_V1_Data.Tv_Unknown ->
          let uu___ =
            FStarC_Reflection_V1_Constants.ref_Tv_Unknown.FStarC_Reflection_V1_Constants.t in
          {
            FStarC_Syntax_Syntax.n = (uu___.FStarC_Syntax_Syntax.n);
            FStarC_Syntax_Syntax.pos = rng;
            FStarC_Syntax_Syntax.vars = (uu___.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (uu___.FStarC_Syntax_Syntax.hash_code)
          }
      | FStarC_Reflection_V1_Data.Tv_Unsupp ->
          let uu___ =
            FStarC_Reflection_V1_Constants.ref_Tv_Unsupp.FStarC_Reflection_V1_Constants.t in
          {
            FStarC_Syntax_Syntax.n = (uu___.FStarC_Syntax_Syntax.n);
            FStarC_Syntax_Syntax.pos = rng;
            FStarC_Syntax_Syntax.vars = (uu___.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (uu___.FStarC_Syntax_Syntax.hash_code)
          } in
    let unembed_term_view t =
      let uu___ = FStarC_Syntax_Util.head_and_args t in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Util.un_uinst hd in
              uu___3.FStarC_Syntax_Syntax.n in
            (uu___2, args) in
          (match uu___1 with
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Var.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_bv b in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun b1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Tv_Var b1))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_BVar.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_bv b in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun b1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Tv_BVar b1))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (f, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_FVar.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed FStarC_Reflection_V2_Embeddings.e_fv f in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun f1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Tv_FVar f1))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (f, uu___2)::(us, uu___3)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_UInst.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed FStarC_Reflection_V2_Embeddings.e_fv f in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun f1 ->
                    let uu___5 =
                      unembed
                        (FStarC_Syntax_Embeddings.e_list
                           FStarC_Reflection_V2_Embeddings.e_universe) us in
                    FStarC_Compiler_Util.bind_opt uu___5
                      (fun us1 ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V1_Data.Tv_UInst (f1, us1))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::(r, uu___3)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_App.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed e_term l in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun l1 ->
                    let uu___5 = unembed e_argv r in
                    FStarC_Compiler_Util.bind_opt uu___5
                      (fun r1 ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V1_Data.Tv_App (l1, r1))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Abs.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___4 =
                 unembed FStarC_Reflection_V2_Embeddings.e_binder b in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 = unembed e_term t1 in
                    FStarC_Compiler_Util.bind_opt uu___5
                      (fun t2 ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V1_Data.Tv_Abs (b1, t2))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (b, uu___2)::(t1, uu___3)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Arrow.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___4 =
                 unembed FStarC_Reflection_V2_Embeddings.e_binder b in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun b1 ->
                    let uu___5 =
                      unembed FStarC_Reflection_V2_Embeddings.e_comp t1 in
                    FStarC_Compiler_Util.bind_opt uu___5
                      (fun c ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V1_Data.Tv_Arrow (b1, c))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Type.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 =
                 unembed FStarC_Reflection_V2_Embeddings.e_universe u in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun u1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Tv_Type u1))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (b, uu___2)::(sort, uu___3)::(t1, uu___4)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Refine.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___5 = unembed e_bv b in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun b1 ->
                    let uu___6 = unembed e_term sort in
                    FStarC_Compiler_Util.bind_opt uu___6
                      (fun sort1 ->
                         let uu___7 = unembed e_term t1 in
                         FStarC_Compiler_Util.bind_opt uu___7
                           (fun t2 ->
                              FStar_Pervasives_Native.Some
                                (FStarC_Reflection_V1_Data.Tv_Refine
                                   (b1, sort1, t2)))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (c, uu___2)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Const.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___3 = unembed e_const c in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun c1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Tv_Const c1))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, (u, uu___2)::(l, uu___3)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Uvar.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___4 = unembed FStarC_Syntax_Embeddings.e_int u in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun u1 ->
                    let ctx_u_s =
                      FStarC_Syntax_Util.unlazy_as_t
                        FStarC_Syntax_Syntax.Lazy_uvar l in
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V1_Data.Tv_Uvar (u1, ctx_u_s)))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (r, uu___2)::(attrs, uu___3)::(b, uu___4)::(ty, uu___5)::
              (t1, uu___6)::(t2, uu___7)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Let.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___8 = unembed FStarC_Syntax_Embeddings.e_bool r in
               FStarC_Compiler_Util.bind_opt uu___8
                 (fun r1 ->
                    let uu___9 =
                      unembed (FStarC_Syntax_Embeddings.e_list e_term) attrs in
                    FStarC_Compiler_Util.bind_opt uu___9
                      (fun attrs1 ->
                         let uu___10 = unembed e_bv b in
                         FStarC_Compiler_Util.bind_opt uu___10
                           (fun b1 ->
                              let uu___11 = unembed e_term ty in
                              FStarC_Compiler_Util.bind_opt uu___11
                                (fun ty1 ->
                                   let uu___12 = unembed e_term t1 in
                                   FStarC_Compiler_Util.bind_opt uu___12
                                     (fun t11 ->
                                        let uu___13 = unembed e_term t2 in
                                        FStarC_Compiler_Util.bind_opt uu___13
                                          (fun t21 ->
                                             FStar_Pervasives_Native.Some
                                               (FStarC_Reflection_V1_Data.Tv_Let
                                                  (r1, attrs1, b1, ty1, t11,
                                                    t21))))))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (t1, uu___2)::(ret_opt, uu___3)::(brs, uu___4)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Match.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___5 = unembed e_term t1 in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun t2 ->
                    let uu___6 = unembed e_match_returns_annotation ret_opt in
                    FStarC_Compiler_Util.bind_opt uu___6
                      (fun ret_opt1 ->
                         let uu___7 =
                           unembed (FStarC_Syntax_Embeddings.e_list e_branch)
                             brs in
                         FStarC_Compiler_Util.bind_opt uu___7
                           (fun brs1 ->
                              FStar_Pervasives_Native.Some
                                (FStarC_Reflection_V1_Data.Tv_Match
                                   (t2, ret_opt1, brs1)))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (e, uu___2)::(t1, uu___3)::(tacopt, uu___4)::(use_eq, uu___5)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_AscT.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___6 = unembed e_term e in
               FStarC_Compiler_Util.bind_opt uu___6
                 (fun e1 ->
                    let uu___7 = unembed e_term t1 in
                    FStarC_Compiler_Util.bind_opt uu___7
                      (fun t2 ->
                         let uu___8 =
                           unembed (FStarC_Syntax_Embeddings.e_option e_term)
                             tacopt in
                         FStarC_Compiler_Util.bind_opt uu___8
                           (fun tacopt1 ->
                              let uu___9 =
                                unembed FStarC_Syntax_Embeddings.e_bool
                                  use_eq in
                              FStarC_Compiler_Util.bind_opt uu___9
                                (fun use_eq1 ->
                                   FStar_Pervasives_Native.Some
                                     (FStarC_Reflection_V1_Data.Tv_AscribedT
                                        (e1, t2, tacopt1, use_eq1))))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv,
              (e, uu___2)::(c, uu___3)::(tacopt, uu___4)::(use_eq, uu___5)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_AscC.FStarC_Reflection_V1_Constants.lid
               ->
               let uu___6 = unembed e_term e in
               FStarC_Compiler_Util.bind_opt uu___6
                 (fun e1 ->
                    let uu___7 = unembed e_comp c in
                    FStarC_Compiler_Util.bind_opt uu___7
                      (fun c1 ->
                         let uu___8 =
                           unembed (FStarC_Syntax_Embeddings.e_option e_term)
                             tacopt in
                         FStarC_Compiler_Util.bind_opt uu___8
                           (fun tacopt1 ->
                              let uu___9 =
                                unembed FStarC_Syntax_Embeddings.e_bool
                                  use_eq in
                              FStarC_Compiler_Util.bind_opt uu___9
                                (fun use_eq1 ->
                                   FStar_Pervasives_Native.Some
                                     (FStarC_Reflection_V1_Data.Tv_AscribedC
                                        (e1, c1, tacopt1, use_eq1))))))
           | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Unknown.FStarC_Reflection_V1_Constants.lid
               ->
               FStar_Pervasives_Native.Some
                 FStarC_Reflection_V1_Data.Tv_Unknown
           | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V1_Constants.ref_Tv_Unsupp.FStarC_Reflection_V1_Constants.lid
               ->
               FStar_Pervasives_Native.Some
                 FStarC_Reflection_V1_Data.Tv_Unsupp
           | uu___2 -> FStar_Pervasives_Native.None) in
    mk_emb embed_term_view unembed_term_view
      FStarC_Reflection_V1_Constants.fstar_refl_term_view
let (e_term_view :
  FStarC_Reflection_V1_Data.term_view FStarC_Syntax_Embeddings_Base.embedding)
  = e_term_view_aq noaqs
let (e_name :
  Prims.string Prims.list FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_string
let (e_bv_view :
  FStarC_Reflection_V1_Data.bv_view FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_bv_view rng bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed
            (FStarC_Syntax_Embeddings.e_sealed
               FStarC_Syntax_Embeddings.e_string) rng
            bvv.FStarC_Reflection_V1_Data.bv_ppname in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed FStarC_Syntax_Embeddings.e_int rng
              bvv.FStarC_Reflection_V1_Data.bv_index in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        [uu___3] in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.ref_Mk_bv.FStarC_Reflection_V1_Constants.t
      uu___ rng in
  let unembed_bv_view t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (nm, uu___2)::(idx, uu___3)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Mk_bv.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___4 =
               unembed
                 (FStarC_Syntax_Embeddings.e_sealed
                    FStarC_Syntax_Embeddings.e_string) nm in
             FStarC_Compiler_Util.bind_opt uu___4
               (fun nm1 ->
                  let uu___5 = unembed FStarC_Syntax_Embeddings.e_int idx in
                  FStarC_Compiler_Util.bind_opt uu___5
                    (fun idx1 ->
                       FStar_Pervasives_Native.Some
                         {
                           FStarC_Reflection_V1_Data.bv_ppname = nm1;
                           FStarC_Reflection_V1_Data.bv_index = idx1
                         }))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_bv_view unembed_bv_view
    FStarC_Reflection_V1_Constants.fstar_refl_bv_view
let (e_attribute :
  FStarC_Syntax_Syntax.attribute FStarC_Syntax_Embeddings_Base.embedding) =
  e_term
let (e_attributes :
  FStarC_Syntax_Syntax.attribute Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_attribute
let (e_binder_view :
  FStarC_Reflection_V1_Data.binder_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_binder_view rng bview =
    let uu___ =
      let uu___1 =
        let uu___2 = embed e_bv rng bview.FStarC_Reflection_V1_Data.binder_bv in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed e_aqualv rng bview.FStarC_Reflection_V1_Data.binder_qual in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_attributes rng
                bview.FStarC_Reflection_V1_Data.binder_attrs in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term rng bview.FStarC_Reflection_V1_Data.binder_sort in
              FStarC_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.ref_Mk_binder.FStarC_Reflection_V1_Constants.t
      uu___ rng in
  let unembed_binder_view t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            (bv, uu___2)::(q, uu___3)::(attrs, uu___4)::(sort, uu___5)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Mk_binder.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___6 = unembed e_bv bv in
             FStarC_Compiler_Util.bind_opt uu___6
               (fun bv1 ->
                  let uu___7 = unembed e_aqualv q in
                  FStarC_Compiler_Util.bind_opt uu___7
                    (fun q1 ->
                       let uu___8 = unembed e_attributes attrs in
                       FStarC_Compiler_Util.bind_opt uu___8
                         (fun attrs1 ->
                            let uu___9 = unembed e_term sort in
                            FStarC_Compiler_Util.bind_opt uu___9
                              (fun sort1 ->
                                 FStar_Pervasives_Native.Some
                                   {
                                     FStarC_Reflection_V1_Data.binder_bv =
                                       bv1;
                                     FStarC_Reflection_V1_Data.binder_qual =
                                       q1;
                                     FStarC_Reflection_V1_Data.binder_attrs =
                                       attrs1;
                                     FStarC_Reflection_V1_Data.binder_sort =
                                       sort1
                                   }))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_binder_view unembed_binder_view
    FStarC_Reflection_V1_Constants.fstar_refl_binder_view
let (e_comp_view :
  FStarC_Reflection_V1_Data.comp_view FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_comp_view rng cv =
    match cv with
    | FStarC_Reflection_V1_Data.C_Total t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_C_Total.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.C_GTotal t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_C_GTotal.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng pre in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_term rng post in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng pats in
                FStarC_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_C_Lemma.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.C_Eff (us, eff, res, args, decrs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed
                (FStarC_Syntax_Embeddings.e_list
                   FStarC_Reflection_V2_Embeddings.e_universe) rng us in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed FStarC_Syntax_Embeddings.e_string_list rng eff in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng res in
                FStarC_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    embed (FStarC_Syntax_Embeddings.e_list e_argv) rng args in
                  FStarC_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      embed (FStarC_Syntax_Embeddings.e_list e_term) rng
                        decrs in
                    FStarC_Syntax_Syntax.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_C_Eff.FStarC_Reflection_V1_Constants.t
          uu___ rng in
  let unembed_comp_view t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Total.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_term t2 in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.C_Total t3))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_GTotal.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed e_term t2 in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun t3 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.C_GTotal t3))
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            (pre, uu___2)::(post, uu___3)::(pats, uu___4)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Lemma.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___5 = unembed e_term pre in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun pre1 ->
                  let uu___6 = unembed e_term post in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun post1 ->
                       let uu___7 = unembed e_term pats in
                       FStarC_Compiler_Util.bind_opt uu___7
                         (fun pats1 ->
                            FStar_Pervasives_Native.Some
                              (FStarC_Reflection_V1_Data.C_Lemma
                                 (pre1, post1, pats1)))))
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            (us, uu___2)::(eff, uu___3)::(res, uu___4)::(args1, uu___5)::
            (decrs, uu___6)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_C_Eff.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___7 =
               unembed
                 (FStarC_Syntax_Embeddings.e_list
                    FStarC_Reflection_V2_Embeddings.e_universe) us in
             FStarC_Compiler_Util.bind_opt uu___7
               (fun us1 ->
                  let uu___8 =
                    unembed FStarC_Syntax_Embeddings.e_string_list eff in
                  FStarC_Compiler_Util.bind_opt uu___8
                    (fun eff1 ->
                       let uu___9 = unembed e_term res in
                       FStarC_Compiler_Util.bind_opt uu___9
                         (fun res1 ->
                            let uu___10 =
                              unembed
                                (FStarC_Syntax_Embeddings.e_list e_argv)
                                args1 in
                            FStarC_Compiler_Util.bind_opt uu___10
                              (fun args2 ->
                                 let uu___11 =
                                   unembed
                                     (FStarC_Syntax_Embeddings.e_list e_term)
                                     decrs in
                                 FStarC_Compiler_Util.bind_opt uu___11
                                   (fun decrs1 ->
                                      FStar_Pervasives_Native.Some
                                        (FStarC_Reflection_V1_Data.C_Eff
                                           (us1, eff1, res1, args2, decrs1)))))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_comp_view unembed_comp_view
    FStarC_Reflection_V1_Constants.fstar_refl_comp_view
let (e_sigelt :
  FStarC_Syntax_Syntax.sigelt FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_sigelt rng se =
    FStarC_Syntax_Util.mk_lazy se
      FStarC_Reflection_V1_Constants.fstar_refl_sigelt
      FStarC_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng) in
  let unembed_sigelt t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_lazy
        { FStarC_Syntax_Syntax.blob = b;
          FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_sigelt;
          FStarC_Syntax_Syntax.ltyp = uu___1;
          FStarC_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_sigelt unembed_sigelt
    FStarC_Reflection_V1_Constants.fstar_refl_sigelt
let (e_univ_name :
  FStarC_Reflection_V1_Data.univ_name FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.set_type
    FStarC_Reflection_V1_Constants.fstar_refl_univ_name e_ident
let (e_lb_view :
  FStarC_Reflection_V1_Data.lb_view FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_lb_view rng lbv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStarC_Reflection_V2_Embeddings.e_fv rng
            lbv.FStarC_Reflection_V1_Data.lb_fv in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed (FStarC_Syntax_Embeddings.e_list e_ident) rng
              lbv.FStarC_Reflection_V1_Data.lb_us in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_term rng lbv.FStarC_Reflection_V1_Data.lb_typ in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term rng lbv.FStarC_Reflection_V1_Data.lb_def in
              FStarC_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.ref_Mk_lb.FStarC_Reflection_V1_Constants.t
      uu___ rng in
  let unembed_lb_view t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            (fv', uu___2)::(us, uu___3)::(typ, uu___4)::(def, uu___5)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Mk_lb.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___6 = unembed FStarC_Reflection_V2_Embeddings.e_fv fv' in
             FStarC_Compiler_Util.bind_opt uu___6
               (fun fv'1 ->
                  let uu___7 =
                    unembed (FStarC_Syntax_Embeddings.e_list e_ident) us in
                  FStarC_Compiler_Util.bind_opt uu___7
                    (fun us1 ->
                       let uu___8 = unembed e_term typ in
                       FStarC_Compiler_Util.bind_opt uu___8
                         (fun typ1 ->
                            let uu___9 = unembed e_term def in
                            FStarC_Compiler_Util.bind_opt uu___9
                              (fun def1 ->
                                 FStar_Pervasives_Native.Some
                                   {
                                     FStarC_Reflection_V1_Data.lb_fv = fv'1;
                                     FStarC_Reflection_V1_Data.lb_us = us1;
                                     FStarC_Reflection_V1_Data.lb_typ = typ1;
                                     FStarC_Reflection_V1_Data.lb_def = def1
                                   }))))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_lb_view unembed_lb_view
    FStarC_Reflection_V1_Constants.fstar_refl_lb_view
let (e_letbinding :
  FStarC_Syntax_Syntax.letbinding FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_letbinding rng lb =
    FStarC_Syntax_Util.mk_lazy lb
      FStarC_Reflection_V1_Constants.fstar_refl_letbinding
      FStarC_Syntax_Syntax.Lazy_letbinding (FStar_Pervasives_Native.Some rng) in
  let unembed_letbinding t =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_lazy
        { FStarC_Syntax_Syntax.blob = lb;
          FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_letbinding;
          FStarC_Syntax_Syntax.ltyp = uu___1;
          FStarC_Syntax_Syntax.rng = uu___2;_}
        ->
        let uu___3 = FStarC_Dyn.undyn lb in
        FStar_Pervasives_Native.Some uu___3
    | uu___1 -> FStar_Pervasives_Native.None in
  mk_emb embed_letbinding unembed_letbinding
    FStarC_Reflection_V1_Constants.fstar_refl_letbinding
let (e_ctor :
  FStarC_Reflection_V1_Data.ctor FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_tuple2
    (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_string)
    e_term
let (e_sigelt_view :
  FStarC_Reflection_V1_Data.sigelt_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_sigelt_view rng sev =
    match sev with
    | FStarC_Reflection_V1_Data.Sg_Let (r, lbs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_bool rng r in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed
                  (FStarC_Syntax_Embeddings.e_list
                     FStarC_Reflection_V2_Embeddings.e_letbinding) rng lbs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Sg_Let.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng nm in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStarC_Syntax_Embeddings.e_list e_ident) rng univs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  embed FStarC_Reflection_V2_Embeddings.e_binders rng bs in
                FStarC_Syntax_Syntax.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 = embed e_term rng t in
                  FStarC_Syntax_Syntax.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      embed (FStarC_Syntax_Embeddings.e_list e_ctor) rng dcs in
                    FStarC_Syntax_Syntax.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Sg_Inductive.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Sg_Val (nm, univs, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng nm in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStarC_Syntax_Embeddings.e_list e_ident) rng univs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng t in
                FStarC_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V1_Constants.ref_Sg_Val.FStarC_Reflection_V1_Constants.t
          uu___ rng
    | FStarC_Reflection_V1_Data.Unk ->
        let uu___ =
          FStarC_Reflection_V1_Constants.ref_Unk.FStarC_Reflection_V1_Constants.t in
        {
          FStarC_Syntax_Syntax.n = (uu___.FStarC_Syntax_Syntax.n);
          FStarC_Syntax_Syntax.pos = rng;
          FStarC_Syntax_Syntax.vars = (uu___.FStarC_Syntax_Syntax.vars);
          FStarC_Syntax_Syntax.hash_code =
            (uu___.FStarC_Syntax_Syntax.hash_code)
        } in
  let unembed_sigelt_view t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(us, uu___3)::(bs, uu___4)::(t2, uu___5)::(dcs,
                                                                    uu___6)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Sg_Inductive.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___7 = unembed FStarC_Syntax_Embeddings.e_string_list nm in
             FStarC_Compiler_Util.bind_opt uu___7
               (fun nm1 ->
                  let uu___8 =
                    unembed (FStarC_Syntax_Embeddings.e_list e_ident) us in
                  FStarC_Compiler_Util.bind_opt uu___8
                    (fun us1 ->
                       let uu___9 =
                         unembed FStarC_Reflection_V2_Embeddings.e_binders bs in
                       FStarC_Compiler_Util.bind_opt uu___9
                         (fun bs1 ->
                            let uu___10 = unembed e_term t2 in
                            FStarC_Compiler_Util.bind_opt uu___10
                              (fun t3 ->
                                 let uu___11 =
                                   unembed
                                     (FStarC_Syntax_Embeddings.e_list e_ctor)
                                     dcs in
                                 FStarC_Compiler_Util.bind_opt uu___11
                                   (fun dcs1 ->
                                      FStar_Pervasives_Native.Some
                                        (FStarC_Reflection_V1_Data.Sg_Inductive
                                           (nm1, us1, bs1, t3, dcs1)))))))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (r, uu___2)::(lbs, uu___3)::[])
             when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Sg_Let.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___4 = unembed FStarC_Syntax_Embeddings.e_bool r in
             FStarC_Compiler_Util.bind_opt uu___4
               (fun r1 ->
                  let uu___5 =
                    unembed
                      (FStarC_Syntax_Embeddings.e_list
                         FStarC_Reflection_V2_Embeddings.e_letbinding) lbs in
                  FStarC_Compiler_Util.bind_opt uu___5
                    (fun lbs1 ->
                       FStar_Pervasives_Native.Some
                         (FStarC_Reflection_V1_Data.Sg_Let (r1, lbs1))))
         | (FStarC_Syntax_Syntax.Tm_fvar fv,
            (nm, uu___2)::(us, uu___3)::(t2, uu___4)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Sg_Val.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___5 = unembed FStarC_Syntax_Embeddings.e_string_list nm in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun nm1 ->
                  let uu___6 =
                    unembed (FStarC_Syntax_Embeddings.e_list e_ident) us in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun us1 ->
                       let uu___7 = unembed e_term t2 in
                       FStarC_Compiler_Util.bind_opt uu___7
                         (fun t3 ->
                            FStar_Pervasives_Native.Some
                              (FStarC_Reflection_V1_Data.Sg_Val
                                 (nm1, us1, t3)))))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_Unk.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Unk
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStarC_Reflection_V1_Constants.fstar_refl_sigelt_view
let (e_qualifier :
  FStarC_Reflection_V1_Data.qualifier FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed1 rng q =
    let r =
      match q with
      | FStarC_Reflection_V1_Data.Assumption ->
          FStarC_Reflection_V1_Constants.ref_qual_Assumption.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.InternalAssumption ->
          FStarC_Reflection_V1_Constants.ref_qual_InternalAssumption.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.New ->
          FStarC_Reflection_V1_Constants.ref_qual_New.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Private ->
          FStarC_Reflection_V1_Constants.ref_qual_Private.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Unfold_for_unification_and_vcgen ->
          FStarC_Reflection_V1_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Visible_default ->
          FStarC_Reflection_V1_Constants.ref_qual_Visible_default.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Irreducible ->
          FStarC_Reflection_V1_Constants.ref_qual_Irreducible.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Inline_for_extraction ->
          FStarC_Reflection_V1_Constants.ref_qual_Inline_for_extraction.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.NoExtract ->
          FStarC_Reflection_V1_Constants.ref_qual_NoExtract.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Noeq ->
          FStarC_Reflection_V1_Constants.ref_qual_Noeq.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Unopteq ->
          FStarC_Reflection_V1_Constants.ref_qual_Unopteq.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.TotalEffect ->
          FStarC_Reflection_V1_Constants.ref_qual_TotalEffect.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Logic ->
          FStarC_Reflection_V1_Constants.ref_qual_Logic.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Reifiable ->
          FStarC_Reflection_V1_Constants.ref_qual_Reifiable.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.ExceptionConstructor ->
          FStarC_Reflection_V1_Constants.ref_qual_ExceptionConstructor.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.HasMaskedEffect ->
          FStarC_Reflection_V1_Constants.ref_qual_HasMaskedEffect.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Effect ->
          FStarC_Reflection_V1_Constants.ref_qual_Effect.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.OnlyName ->
          FStarC_Reflection_V1_Constants.ref_qual_OnlyName.FStarC_Reflection_V1_Constants.t
      | FStarC_Reflection_V1_Data.Reflectable l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng l in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_qual_Reflectable.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.Discriminator l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng l in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_qual_Discriminator.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.Action l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng l in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_qual_Action.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.Projector (l, i) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     FStarC_Syntax_Embeddings.e_string_list e_ident) rng
                  (l, i) in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_qual_Projector.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.RecordType (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     (FStarC_Syntax_Embeddings.e_list e_ident)
                     (FStarC_Syntax_Embeddings.e_list e_ident)) rng
                  (ids1, ids2) in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_qual_RecordType.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V1_Data.RecordConstructor (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     (FStarC_Syntax_Embeddings.e_list e_ident)
                     (FStarC_Syntax_Embeddings.e_list e_ident)) rng
                  (ids1, ids2) in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V1_Constants.ref_qual_RecordConstructor.FStarC_Reflection_V1_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed1 t =
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Util.un_uinst hd in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Assumption.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Assumption
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_InternalAssumption.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.InternalAssumption
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_New.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.New
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Private.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Private
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Unfold_for_unification_and_vcgen
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Visible_default.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Visible_default
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Irreducible.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Irreducible
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Inline_for_extraction.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.Inline_for_extraction
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_NoExtract.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.NoExtract
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Noeq.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Noeq
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Unopteq.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Unopteq
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_TotalEffect.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.TotalEffect
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Logic.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Logic
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Reifiable.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Reifiable
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_ExceptionConstructor.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.ExceptionConstructor
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_HasMaskedEffect.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some
               FStarC_Reflection_V1_Data.HasMaskedEffect
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Effect.FStarC_Reflection_V1_Constants.lid
             -> FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.Effect
         | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_OnlyName.FStarC_Reflection_V1_Constants.lid
             ->
             FStar_Pervasives_Native.Some FStarC_Reflection_V1_Data.OnlyName
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Reflectable.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_string_list l in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Reflectable l1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Discriminator.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_string_list l in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Discriminator l1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (l, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Action.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 = unembed FStarC_Syntax_Embeddings.e_string_list l in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun l1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V1_Data.Action l1))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_Projector.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStarC_Syntax_Embeddings.e_tuple2
                    FStarC_Syntax_Embeddings.e_string_list e_ident) payload in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (l, i) ->
                      FStar_Pervasives_Native.Some
                        (FStarC_Reflection_V1_Data.Projector (l, i)))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_RecordType.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStarC_Syntax_Embeddings.e_tuple2
                    (FStarC_Syntax_Embeddings.e_list e_ident)
                    (FStarC_Syntax_Embeddings.e_list e_ident)) payload in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (ids1, ids2) ->
                      FStar_Pervasives_Native.Some
                        (FStarC_Reflection_V1_Data.RecordType (ids1, ids2)))
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (payload, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Reflection_V1_Constants.ref_qual_RecordConstructor.FStarC_Reflection_V1_Constants.lid
             ->
             let uu___3 =
               unembed
                 (FStarC_Syntax_Embeddings.e_tuple2
                    (FStarC_Syntax_Embeddings.e_list e_ident)
                    (FStarC_Syntax_Embeddings.e_list e_ident)) payload in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun uu___4 ->
                  match uu___4 with
                  | (ids1, ids2) ->
                      FStar_Pervasives_Native.Some
                        (FStarC_Reflection_V1_Data.RecordConstructor
                           (ids1, ids2)))
         | uu___2 -> FStar_Pervasives_Native.None) in
  mk_emb embed1 unembed1 FStarC_Reflection_V1_Constants.fstar_refl_qualifier
let (e_qualifiers :
  FStarC_Reflection_V1_Data.qualifier Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_qualifier
let (unfold_lazy_bv :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let bv = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V1_Builtins.inspect_bv bv in
          embed e_bv_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_bv.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let binder = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V1_Builtins.inspect_binder binder in
          embed e_binder_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_binder.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_letbinding :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let lb = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let lbv = FStarC_Reflection_V1_Builtins.inspect_lb lb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStarC_Reflection_V2_Embeddings.e_fv
            i.FStarC_Syntax_Syntax.rng lbv.FStarC_Reflection_V1_Data.lb_fv in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed (FStarC_Syntax_Embeddings.e_list e_ident)
              i.FStarC_Syntax_Syntax.rng lbv.FStarC_Reflection_V1_Data.lb_us in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_term i.FStarC_Syntax_Syntax.rng
                lbv.FStarC_Reflection_V1_Data.lb_typ in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term i.FStarC_Syntax_Syntax.rng
                  lbv.FStarC_Reflection_V1_Data.lb_def in
              FStarC_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_lb.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_fvar :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let fv = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V1_Builtins.inspect_fv fv in
          embed FStarC_Syntax_Embeddings.e_string_list
            i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_fv.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_comp :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let comp = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V1_Builtins.inspect_comp comp in
          embed e_comp_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_comp.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_env :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i -> FStarC_Syntax_Util.exp_unit
let (unfold_lazy_optionstate :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i -> FStarC_Syntax_Util.exp_unit
let (unfold_lazy_sigelt :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let sigelt = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V1_Builtins.inspect_sigelt sigelt in
          embed e_sigelt_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_sigelt.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_universe :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let u = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V1_Builtins.inspect_universe u in
          embed e_universe_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V1_Constants.fstar_refl_pack_universe.FStarC_Reflection_V1_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng