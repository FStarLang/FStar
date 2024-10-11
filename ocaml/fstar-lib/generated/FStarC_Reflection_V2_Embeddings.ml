open Prims
type namedv = FStarC_Syntax_Syntax.bv
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
let try_unembed :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      FStarC_Syntax_Embeddings_Base.try_unembed uu___ x
        FStarC_Syntax_Embeddings_Base.id_norm_cb
let curry :
  'uuuuu 'uuuuu1 'uuuuu2 .
    (('uuuuu * 'uuuuu1) -> 'uuuuu2) -> 'uuuuu -> 'uuuuu1 -> 'uuuuu2
  = fun f -> fun x -> fun y -> f (x, y)
let curry3 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    (('uuuuu * 'uuuuu1 * 'uuuuu2) -> 'uuuuu3) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3
  = fun f -> fun x -> fun y -> fun z -> f (x, y, z)
let curry4 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 .
    (('uuuuu * 'uuuuu1 * 'uuuuu2 * 'uuuuu3) -> 'uuuuu4) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4
  = fun f -> fun x -> fun y -> fun z -> fun w -> f (x, y, z, w)
let curry5 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    (('uuuuu * 'uuuuu1 * 'uuuuu2 * 'uuuuu3 * 'uuuuu4) -> 'uuuuu5) ->
      'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4 -> 'uuuuu5
  = fun f -> fun x -> fun y -> fun z -> fun w -> fun v -> f (x, y, z, w, v)
let (head_fv_and_args :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.args)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = FStarC_Syntax_Util.unascribe t in
    let uu___ = FStarC_Syntax_Util.head_and_args t1 in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Util.un_uinst hd in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, args)
         | uu___2 -> FStar_Pervasives_Native.None)
let (noaqs : FStarC_Syntax_Syntax.antiquotations) = (Prims.int_zero, [])
let (e_bv : FStarC_Syntax_Syntax.bv FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_bv
    FStarC_Reflection_V2_Constants.fstar_refl_bv
let (e_namedv : namedv FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_namedv
    FStarC_Reflection_V2_Constants.fstar_refl_namedv
let (e_binder :
  FStarC_Syntax_Syntax.binder FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_binder
    FStarC_Reflection_V2_Constants.fstar_refl_binder
let (e_fv : FStarC_Syntax_Syntax.fv FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_fvar
    FStarC_Reflection_V2_Constants.fstar_refl_fv
let (e_comp :
  FStarC_Syntax_Syntax.comp FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_comp
    FStarC_Reflection_V2_Constants.fstar_refl_comp
let (e_universe :
  FStarC_Syntax_Syntax.universe FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_universe
    FStarC_Reflection_V2_Constants.fstar_refl_universe
let (e_ident : FStarC_Ident.ident FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_ident
    FStarC_Reflection_V2_Constants.fstar_refl_ident
let (e_env :
  FStarC_TypeChecker_Env.env FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_env
    FStarC_Reflection_V2_Constants.fstar_refl_env
let (e_sigelt :
  FStarC_Syntax_Syntax.sigelt FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_sigelt
    FStarC_Reflection_V2_Constants.fstar_refl_sigelt
let (e_letbinding :
  FStarC_Syntax_Syntax.letbinding FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_letbinding
    FStarC_Reflection_V2_Constants.fstar_refl_letbinding
let (e_ctx_uvar_and_subst :
  FStarC_Syntax_Syntax.ctx_uvar_and_subst
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.e_lazy FStarC_Syntax_Syntax.Lazy_uvar
    FStarC_Reflection_V2_Constants.fstar_refl_ctx_uvar_and_subst
let (e_universe_uvar :
  FStarC_Syntax_Syntax.universe_uvar FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.e_lazy
    FStarC_Syntax_Syntax.Lazy_universe_uvar
    FStarC_Reflection_V2_Constants.fstar_refl_universe_uvar
let rec mapM_opt :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          let uu___ = f x in
          FStarC_Compiler_Util.bind_opt uu___
            (fun x1 ->
               let uu___1 = mapM_opt f xs in
               FStarC_Compiler_Util.bind_opt uu___1
                 (fun xs1 -> FStar_Pervasives_Native.Some (x1 :: xs1)))
let (e_term_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let embed_term rng t =
      let qi =
        {
          FStarC_Syntax_Syntax.qkind = FStarC_Syntax_Syntax.Quote_static;
          FStarC_Syntax_Syntax.antiquotations = aq
        } in
      FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_quoted (t, qi)) rng in
    let rec unembed_term t =
      let apply_antiquotations t1 aq1 =
        let uu___ = aq1 in
        match uu___ with
        | (shift, aqs) ->
            let aqs1 = FStarC_Compiler_List.rev aqs in
            let uu___1 = mapM_opt unembed_term aqs1 in
            FStarC_Compiler_Util.bind_opt uu___1
              (fun aq_ts ->
                 let uu___2 =
                   let uu___3 =
                     FStarC_Compiler_List.mapi
                       (fun i ->
                          fun at ->
                            let x =
                              FStarC_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStarC_Syntax_Syntax.t_term in
                            ((FStarC_Syntax_Syntax.DB ((shift + i), x)),
                              (FStarC_Syntax_Syntax.NT (x, at)))) aq_ts in
                   FStarC_Compiler_List.unzip uu___3 in
                 match uu___2 with
                 | (subst_open, subst) ->
                     let uu___3 =
                       let uu___4 = FStarC_Syntax_Subst.subst subst_open t1 in
                       FStarC_Syntax_Subst.subst subst uu___4 in
                     FStar_Pervasives_Native.Some uu___3) in
      let t1 = FStarC_Syntax_Util.unmeta t in
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t1 in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_quoted (tm, qi) ->
          apply_antiquotations tm qi.FStarC_Syntax_Syntax.antiquotations
      | uu___1 -> FStar_Pervasives_Native.None in
    mk_emb embed_term unembed_term FStarC_Syntax_Syntax.t_term
let (e_term :
  FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding) =
  e_term_aq noaqs
let (e_sort :
  FStarC_Syntax_Syntax.term FStarC_Compiler_Sealed.sealed
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_sealed e_term
let (e_ppname :
  FStarC_Reflection_V2_Data.ppname_t FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_sealed FStarC_Syntax_Embeddings.e_string
let (e_aqualv :
  FStarC_Reflection_V2_Data.aqualv FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_aqualv rng q =
    let r =
      match q with
      | FStarC_Reflection_V2_Data.Q_Explicit ->
          FStarC_Reflection_V2_Constants.ref_Q_Explicit.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Q_Implicit ->
          FStarC_Reflection_V2_Constants.ref_Q_Implicit.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Q_Equality ->
          FStarC_Reflection_V2_Constants.ref_Q_Equality.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Q_Meta t ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_term rng t in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Q_Meta.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed_aqualv t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Q_Explicit.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 FStarC_Syntax_Embeddings_AppEmb.pure
                   FStarC_Reflection_V2_Data.Q_Explicit in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_Q_Implicit.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    FStarC_Syntax_Embeddings_AppEmb.pure
                      FStarC_Reflection_V2_Data.Q_Implicit in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_Q_Equality.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      FStarC_Syntax_Embeddings_AppEmb.pure
                        FStarC_Reflection_V2_Data.Q_Equality in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_Q_Meta.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 ->
                             FStarC_Reflection_V2_Data.Q_Meta uu___3) e_term in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else FStar_Pervasives_Native.None) in
  mk_emb embed_aqualv unembed_aqualv
    FStarC_Reflection_V2_Constants.fstar_refl_aqualv
let (e_binders :
  FStarC_Syntax_Syntax.binders FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_list e_binder
let (e_universe_view :
  FStarC_Reflection_V2_Data.universe_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_universe_view rng uv =
    match uv with
    | FStarC_Reflection_V2_Data.Uv_Zero ->
        FStarC_Reflection_V2_Constants.ref_Uv_Zero.FStarC_Reflection_V2_Constants.t
    | FStarC_Reflection_V2_Data.Uv_Succ u ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_universe rng u in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Uv_Succ.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Uv_Max us ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed (FStarC_Syntax_Embeddings.e_list e_universe) rng us in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Uv_Max.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Uv_BVar n ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_int rng n in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Uv_BVar.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Uv_Name i ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_ident rng i in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Uv_Name.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Uv_Unif u ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_universe_uvar rng u in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Uv_Unif.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Uv_Unk ->
        FStarC_Reflection_V2_Constants.ref_Uv_Unk.FStarC_Reflection_V2_Constants.t in
  let unembed_universe_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Uv_Zero.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 FStarC_Syntax_Embeddings_AppEmb.pure
                   FStarC_Reflection_V2_Data.Uv_Zero in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_Uv_Succ.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                      (fun uu___3 -> FStarC_Reflection_V2_Data.Uv_Succ uu___3)
                      e_universe in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_Uv_Max.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                        (fun uu___3 ->
                           FStarC_Reflection_V2_Data.Uv_Max uu___3)
                        (FStarC_Syntax_Embeddings.e_list e_universe) in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_Uv_BVar.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 ->
                             FStarC_Reflection_V2_Data.Uv_BVar uu___3)
                          FStarC_Syntax_Embeddings.e_int in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Reflection_V2_Constants.ref_Uv_Name.FStarC_Reflection_V2_Constants.lid
                     then
                       (let uu___2 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (fun uu___3 ->
                               FStarC_Reflection_V2_Data.Uv_Name uu___3)
                            e_ident in
                        FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                     else
                       if
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Reflection_V2_Constants.ref_Uv_Unif.FStarC_Reflection_V2_Constants.lid
                       then
                         (let uu___2 =
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                              (fun uu___3 ->
                                 FStarC_Reflection_V2_Data.Uv_Unif uu___3)
                              e_universe_uvar in
                          FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                       else
                         if
                           FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Reflection_V2_Constants.ref_Uv_Unk.FStarC_Reflection_V2_Constants.lid
                         then
                           (let uu___2 =
                              FStarC_Syntax_Embeddings_AppEmb.pure
                                FStarC_Reflection_V2_Data.Uv_Unk in
                            FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                         else FStar_Pervasives_Native.None) in
  mk_emb embed_universe_view unembed_universe_view
    FStarC_Reflection_V2_Constants.fstar_refl_universe_view
let (e_vconst :
  FStarC_Reflection_V2_Data.vconst FStarC_Syntax_Embeddings_Base.embedding) =
  let embed_const rng c =
    let r =
      match c with
      | FStarC_Reflection_V2_Data.C_Unit ->
          FStarC_Reflection_V2_Constants.ref_C_Unit.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.C_True ->
          FStarC_Reflection_V2_Constants.ref_C_True.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.C_False ->
          FStarC_Reflection_V2_Constants.ref_C_False.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.C_Int i ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_BigInt.string_of_big_int i in
                FStarC_Syntax_Util.exp_int uu___3 in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_C_Int.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.C_String s ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string rng s in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_C_String.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.C_Range r1 ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_range rng r1 in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_C_Range.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.C_Reify ->
          FStarC_Reflection_V2_Constants.ref_C_Reify.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.C_Reflect ns ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed FStarC_Syntax_Embeddings.e_string_list rng ns in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_C_Reflect.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.C_Real s ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string rng s in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_C_Real.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed_const t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_C_Unit.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 FStarC_Syntax_Embeddings_AppEmb.pure
                   FStarC_Reflection_V2_Data.C_Unit in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_C_True.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    FStarC_Syntax_Embeddings_AppEmb.pure
                      FStarC_Reflection_V2_Data.C_True in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_C_False.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      FStarC_Syntax_Embeddings_AppEmb.pure
                        FStarC_Reflection_V2_Data.C_False in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_C_Int.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 ->
                             FStarC_Reflection_V2_Data.C_Int uu___3)
                          FStarC_Syntax_Embeddings.e_int in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Reflection_V2_Constants.ref_C_String.FStarC_Reflection_V2_Constants.lid
                     then
                       (let uu___2 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (fun uu___3 ->
                               FStarC_Reflection_V2_Data.C_String uu___3)
                            FStarC_Syntax_Embeddings.e_string in
                        FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                     else
                       if
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Reflection_V2_Constants.ref_C_Range.FStarC_Reflection_V2_Constants.lid
                       then
                         (let uu___2 =
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                              (fun uu___3 ->
                                 FStarC_Reflection_V2_Data.C_Range uu___3)
                              FStarC_Syntax_Embeddings.e_range in
                          FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                       else
                         if
                           FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Reflection_V2_Constants.ref_C_Reify.FStarC_Reflection_V2_Constants.lid
                         then
                           (let uu___2 =
                              FStarC_Syntax_Embeddings_AppEmb.pure
                                FStarC_Reflection_V2_Data.C_Reify in
                            FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                         else
                           if
                             FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Reflection_V2_Constants.ref_C_Reflect.FStarC_Reflection_V2_Constants.lid
                           then
                             (let uu___2 =
                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                  (fun uu___3 ->
                                     FStarC_Reflection_V2_Data.C_Reflect
                                       uu___3)
                                  FStarC_Syntax_Embeddings.e_string_list in
                              FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                           else
                             if
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Reflection_V2_Constants.ref_C_Real.FStarC_Reflection_V2_Constants.lid
                             then
                               (let uu___2 =
                                  FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                    (fun uu___3 ->
                                       FStarC_Reflection_V2_Data.C_Real
                                         uu___3)
                                    FStarC_Syntax_Embeddings.e_string in
                                FStarC_Syntax_Embeddings_AppEmb.run args
                                  uu___2)
                             else FStar_Pervasives_Native.None) in
  mk_emb embed_const unembed_const
    FStarC_Reflection_V2_Constants.fstar_refl_vconst
let rec e_pattern_aq :
  'uuuuu .
    'uuuuu ->
      FStarC_Reflection_V2_Data.pattern
        FStarC_Syntax_Embeddings_Base.embedding
  =
  fun aq ->
    let rec embed_pattern rng p =
      match p with
      | FStarC_Reflection_V2_Data.Pat_Constant c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_vconst rng c in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Pat_Constant.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_fv rng head in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed
                    (FStarC_Syntax_Embeddings.e_option
                       (FStarC_Syntax_Embeddings.e_list e_universe)) rng
                    univs in
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
                    embed uu___7 rng subpats in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Pat_Cons.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Pat_Var (sort, ppname) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_sort rng sort in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed
                    (FStarC_Syntax_Embeddings.e_sealed
                       FStarC_Syntax_Embeddings.e_string) rng ppname in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Pat_Var.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Pat_Dot_Term eopt ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed (FStarC_Syntax_Embeddings.e_option e_term) rng eopt in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Pat_Dot_Term.FStarC_Reflection_V2_Constants.t
            uu___ rng in
    let rec unembed_pattern t =
      let uu___ = head_fv_and_args t in
      FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (fv, args) ->
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_Pat_Constant.FStarC_Reflection_V2_Constants.lid
               then
                 let uu___2 =
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                     (fun uu___3 ->
                        FStarC_Reflection_V2_Data.Pat_Constant uu___3)
                     e_vconst in
                 FStarC_Syntax_Embeddings_AppEmb.run args uu___2
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_Pat_Cons.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (fun uu___5 ->
                               fun uu___6 ->
                                 fun uu___7 ->
                                   FStarC_Reflection_V2_Data.Pat_Cons
                                     (uu___5, uu___6, uu___7)) e_fv in
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                          uu___4
                          (FStarC_Syntax_Embeddings.e_option
                             (FStarC_Syntax_Embeddings.e_list e_universe)) in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = e_pattern_aq aq in
                          FStarC_Syntax_Embeddings.e_tuple2 uu___6
                            FStarC_Syntax_Embeddings.e_bool in
                        FStarC_Syntax_Embeddings.e_list uu___5 in
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                        uu___3 uu___4 in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_Pat_Var.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        let uu___3 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (fun uu___4 ->
                               fun uu___5 ->
                                 FStarC_Reflection_V2_Data.Pat_Var
                                   (uu___4, uu___5)) e_sort in
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                          uu___3 e_ppname in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Reflection_V2_Constants.ref_Pat_Dot_Term.FStarC_Reflection_V2_Constants.lid
                     then
                       (let uu___2 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (fun uu___3 ->
                               FStarC_Reflection_V2_Data.Pat_Dot_Term uu___3)
                            (FStarC_Syntax_Embeddings.e_option e_term) in
                        FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                     else FStar_Pervasives_Native.None) in
    mk_emb embed_pattern unembed_pattern
      FStarC_Reflection_V2_Constants.fstar_refl_pattern
let (e_pattern :
  FStarC_Reflection_V2_Data.pattern FStarC_Syntax_Embeddings_Base.embedding)
  = e_pattern_aq noaqs
let (e_branch :
  FStarC_Reflection_V2_Data.branch FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_tuple2 e_pattern e_term
let (e_argv :
  FStarC_Reflection_V2_Data.argv FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_tuple2 e_term e_aqualv
let (e_args :
  FStarC_Reflection_V2_Data.argv Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_argv
let (e_branch_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    (FStarC_Reflection_V2_Data.pattern * FStarC_Syntax_Syntax.term)
      FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let uu___ = e_pattern_aq aq in
    let uu___1 = e_term_aq aq in
    FStarC_Syntax_Embeddings.e_tuple2 uu___ uu___1
let (e_argv_aq :
  FStarC_Syntax_Syntax.antiquotations ->
    (FStarC_Syntax_Syntax.term * FStarC_Reflection_V2_Data.aqualv)
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
    FStarC_Reflection_V2_Data.term_view
      FStarC_Syntax_Embeddings_Base.embedding)
  =
  fun aq ->
    let push uu___ =
      match uu___ with | (s, aq1) -> ((s + Prims.int_one), aq1) in
    let embed_term_view rng t =
      match t with
      | FStarC_Reflection_V2_Data.Tv_FVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_fv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_FVar.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_BVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_bv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_BVar.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_namedv rng bv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Var.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_fv rng fv in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  embed (FStarC_Syntax_Embeddings.e_list e_universe) rng us in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_UInst.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_App (hd, a) ->
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
            FStarC_Reflection_V2_Constants.ref_Tv_App.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Abs (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_binder rng b in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in embed uu___5 rng t1 in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Abs.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_binder rng b in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_comp rng c in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Arrow.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_universe rng u in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Type.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Refine (b, t1) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_binder rng b in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = e_term_aq (push aq) in embed uu___5 rng t1 in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Refine.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed e_vconst rng c in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Const.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Uvar (u, ctx_u) ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_int rng u in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_ctx_uvar_and_subst rng ctx_u in
                FStarC_Syntax_Syntax.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Uvar.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Let (r, attrs, b, t1, t2) ->
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
                  let uu___6 = embed e_binder rng b in
                  FStarC_Syntax_Syntax.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      let uu___9 = e_term_aq aq in embed uu___9 rng t1 in
                    FStarC_Syntax_Syntax.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = e_term_aq (push aq) in
                        embed uu___11 rng t2 in
                      FStarC_Syntax_Syntax.as_arg uu___10 in
                    [uu___9] in
                  uu___7 :: uu___8 in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_Tv_Let.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Match (t1, ret_opt, brs) ->
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
            FStarC_Reflection_V2_Constants.ref_Tv_Match.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_AscribedT (e, t1, tacopt, use_eq) ->
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
            FStarC_Reflection_V2_Constants.ref_Tv_AscT.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 = let uu___3 = e_term_aq aq in embed uu___3 rng e in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = embed e_comp rng c in
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
            FStarC_Reflection_V2_Constants.ref_Tv_AscC.FStarC_Reflection_V2_Constants.t
            uu___ rng
      | FStarC_Reflection_V2_Data.Tv_Unknown ->
          let uu___ =
            FStarC_Reflection_V2_Constants.ref_Tv_Unknown.FStarC_Reflection_V2_Constants.t in
          {
            FStarC_Syntax_Syntax.n = (uu___.FStarC_Syntax_Syntax.n);
            FStarC_Syntax_Syntax.pos = rng;
            FStarC_Syntax_Syntax.vars = (uu___.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (uu___.FStarC_Syntax_Syntax.hash_code)
          }
      | FStarC_Reflection_V2_Data.Tv_Unsupp ->
          let uu___ =
            FStarC_Reflection_V2_Constants.ref_Tv_Unsupp.FStarC_Reflection_V2_Constants.t in
          {
            FStarC_Syntax_Syntax.n = (uu___.FStarC_Syntax_Syntax.n);
            FStarC_Syntax_Syntax.pos = rng;
            FStarC_Syntax_Syntax.vars = (uu___.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (uu___.FStarC_Syntax_Syntax.hash_code)
          } in
    let unembed_term_view t =
      let uu___ = head_fv_and_args t in
      FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (fv, args) ->
               let xTv_Let a b c d e =
                 FStarC_Reflection_V2_Data.Tv_Let (a, b, c, d, e) in
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_Tv_FVar.FStarC_Reflection_V2_Constants.lid
               then
                 let uu___2 =
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                     (fun uu___3 -> FStarC_Reflection_V2_Data.Tv_FVar uu___3)
                     e_fv in
                 FStarC_Syntax_Embeddings_AppEmb.run args uu___2
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_Tv_BVar.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                        (fun uu___3 ->
                           FStarC_Reflection_V2_Data.Tv_BVar uu___3) e_bv in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_Tv_Var.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                          (fun uu___3 ->
                             FStarC_Reflection_V2_Data.Tv_Var uu___3)
                          e_namedv in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Reflection_V2_Constants.ref_Tv_UInst.FStarC_Reflection_V2_Constants.lid
                     then
                       (let uu___2 =
                          let uu___3 =
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                              (curry
                                 (fun uu___4 ->
                                    FStarC_Reflection_V2_Data.Tv_UInst uu___4))
                              e_fv in
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                            uu___3
                            (FStarC_Syntax_Embeddings.e_list e_universe) in
                        FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                     else
                       if
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Reflection_V2_Constants.ref_Tv_App.FStarC_Reflection_V2_Constants.lid
                       then
                         (let uu___2 =
                            let uu___3 =
                              let uu___4 = e_term_aq aq in
                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                (curry
                                   (fun uu___5 ->
                                      FStarC_Reflection_V2_Data.Tv_App uu___5))
                                uu___4 in
                            let uu___4 = e_argv_aq aq in
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                              uu___3 uu___4 in
                          FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                       else
                         if
                           FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Reflection_V2_Constants.ref_Tv_Abs.FStarC_Reflection_V2_Constants.lid
                         then
                           (let uu___2 =
                              let uu___3 =
                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                  (curry
                                     (fun uu___4 ->
                                        FStarC_Reflection_V2_Data.Tv_Abs
                                          uu___4)) e_binder in
                              let uu___4 = e_term_aq (push aq) in
                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                uu___3 uu___4 in
                            FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                         else
                           if
                             FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Reflection_V2_Constants.ref_Tv_Arrow.FStarC_Reflection_V2_Constants.lid
                           then
                             (let uu___2 =
                                let uu___3 =
                                  FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                    (curry
                                       (fun uu___4 ->
                                          FStarC_Reflection_V2_Data.Tv_Arrow
                                            uu___4)) e_binder in
                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                  uu___3 e_comp in
                              FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                           else
                             if
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Reflection_V2_Constants.ref_Tv_Type.FStarC_Reflection_V2_Constants.lid
                             then
                               (let uu___2 =
                                  FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                    (fun uu___3 ->
                                       FStarC_Reflection_V2_Data.Tv_Type
                                         uu___3) e_universe in
                                FStarC_Syntax_Embeddings_AppEmb.run args
                                  uu___2)
                             else
                               if
                                 FStarC_Syntax_Syntax.fv_eq_lid fv
                                   FStarC_Reflection_V2_Constants.ref_Tv_Refine.FStarC_Reflection_V2_Constants.lid
                               then
                                 (let uu___2 =
                                    let uu___3 =
                                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                        (curry
                                           (fun uu___4 ->
                                              FStarC_Reflection_V2_Data.Tv_Refine
                                                uu___4)) e_binder in
                                    let uu___4 = e_term_aq (push aq) in
                                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                      uu___3 uu___4 in
                                  FStarC_Syntax_Embeddings_AppEmb.run args
                                    uu___2)
                               else
                                 if
                                   FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Reflection_V2_Constants.ref_Tv_Const.FStarC_Reflection_V2_Constants.lid
                                 then
                                   (let uu___2 =
                                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                        (fun uu___3 ->
                                           FStarC_Reflection_V2_Data.Tv_Const
                                             uu___3) e_vconst in
                                    FStarC_Syntax_Embeddings_AppEmb.run args
                                      uu___2)
                                 else
                                   if
                                     FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Reflection_V2_Constants.ref_Tv_Uvar.FStarC_Reflection_V2_Constants.lid
                                   then
                                     (let uu___2 =
                                        let uu___3 =
                                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                            (curry
                                               (fun uu___4 ->
                                                  FStarC_Reflection_V2_Data.Tv_Uvar
                                                    uu___4))
                                            FStarC_Syntax_Embeddings.e_int in
                                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                          uu___3 e_ctx_uvar_and_subst in
                                      FStarC_Syntax_Embeddings_AppEmb.run
                                        args uu___2)
                                   else
                                     if
                                       FStarC_Syntax_Syntax.fv_eq_lid fv
                                         FStarC_Reflection_V2_Constants.ref_Tv_Let.FStarC_Reflection_V2_Constants.lid
                                     then
                                       (let uu___2 =
                                          let uu___3 =
                                            let uu___4 =
                                              let uu___5 =
                                                let uu___6 =
                                                  FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                    xTv_Let
                                                    FStarC_Syntax_Embeddings.e_bool in
                                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                  uu___6
                                                  (FStarC_Syntax_Embeddings.e_list
                                                     e_term) in
                                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                uu___5 e_binder in
                                            let uu___5 = e_term_aq aq in
                                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                              uu___4 uu___5 in
                                          let uu___4 = e_term_aq (push aq) in
                                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                            uu___3 uu___4 in
                                        FStarC_Syntax_Embeddings_AppEmb.run
                                          args uu___2)
                                     else
                                       if
                                         FStarC_Syntax_Syntax.fv_eq_lid fv
                                           FStarC_Reflection_V2_Constants.ref_Tv_Match.FStarC_Reflection_V2_Constants.lid
                                       then
                                         (let uu___2 =
                                            let uu___3 =
                                              let uu___4 =
                                                let uu___5 = e_term_aq aq in
                                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                  (curry3
                                                     (fun uu___6 ->
                                                        FStarC_Reflection_V2_Data.Tv_Match
                                                          uu___6)) uu___5 in
                                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                uu___4
                                                e_match_returns_annotation in
                                            let uu___4 =
                                              let uu___5 = e_branch_aq aq in
                                              FStarC_Syntax_Embeddings.e_list
                                                uu___5 in
                                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                              uu___3 uu___4 in
                                          FStarC_Syntax_Embeddings_AppEmb.run
                                            args uu___2)
                                       else
                                         if
                                           FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Reflection_V2_Constants.ref_Tv_AscT.FStarC_Reflection_V2_Constants.lid
                                         then
                                           (let uu___2 =
                                              let uu___3 =
                                                let uu___4 =
                                                  let uu___5 =
                                                    let uu___6 = e_term_aq aq in
                                                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                      (curry4
                                                         (fun uu___7 ->
                                                            FStarC_Reflection_V2_Data.Tv_AscribedT
                                                              uu___7)) uu___6 in
                                                  let uu___6 = e_term_aq aq in
                                                  FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                    uu___5 uu___6 in
                                                let uu___5 =
                                                  let uu___6 = e_term_aq aq in
                                                  FStarC_Syntax_Embeddings.e_option
                                                    uu___6 in
                                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                  uu___4 uu___5 in
                                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                uu___3
                                                FStarC_Syntax_Embeddings.e_bool in
                                            FStarC_Syntax_Embeddings_AppEmb.run
                                              args uu___2)
                                         else
                                           if
                                             FStarC_Syntax_Syntax.fv_eq_lid
                                               fv
                                               FStarC_Reflection_V2_Constants.ref_Tv_AscC.FStarC_Reflection_V2_Constants.lid
                                           then
                                             (let uu___2 =
                                                let uu___3 =
                                                  let uu___4 =
                                                    let uu___5 =
                                                      let uu___6 =
                                                        e_term_aq aq in
                                                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                        (curry4
                                                           (fun uu___7 ->
                                                              FStarC_Reflection_V2_Data.Tv_AscribedC
                                                                uu___7))
                                                        uu___6 in
                                                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                      uu___5 e_comp in
                                                  let uu___5 =
                                                    let uu___6 = e_term_aq aq in
                                                    FStarC_Syntax_Embeddings.e_option
                                                      uu___6 in
                                                  FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                    uu___4 uu___5 in
                                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                                  uu___3
                                                  FStarC_Syntax_Embeddings.e_bool in
                                              FStarC_Syntax_Embeddings_AppEmb.run
                                                args uu___2)
                                           else
                                             if
                                               FStarC_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStarC_Reflection_V2_Constants.ref_Tv_Unknown.FStarC_Reflection_V2_Constants.lid
                                             then
                                               (let uu___2 =
                                                  FStarC_Syntax_Embeddings_AppEmb.pure
                                                    FStarC_Reflection_V2_Data.Tv_Unknown in
                                                FStarC_Syntax_Embeddings_AppEmb.run
                                                  args uu___2)
                                             else
                                               if
                                                 FStarC_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStarC_Reflection_V2_Constants.ref_Tv_Unsupp.FStarC_Reflection_V2_Constants.lid
                                               then
                                                 (let uu___2 =
                                                    FStarC_Syntax_Embeddings_AppEmb.pure
                                                      FStarC_Reflection_V2_Data.Tv_Unsupp in
                                                  FStarC_Syntax_Embeddings_AppEmb.run
                                                    args uu___2)
                                               else
                                                 FStar_Pervasives_Native.None) in
    mk_emb embed_term_view unembed_term_view
      FStarC_Reflection_V2_Constants.fstar_refl_term_view
let (e_term_view :
  FStarC_Reflection_V2_Data.term_view FStarC_Syntax_Embeddings_Base.embedding)
  = e_term_view_aq noaqs
let (e_name :
  Prims.string Prims.list FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_string
let (e_namedv_view :
  FStarC_Reflection_V2_Data.namedv_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_namedv_view rng namedvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStarC_Syntax_Embeddings.e_int rng
            namedvv.FStarC_Reflection_V2_Data.uniq in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed e_sort rng namedvv.FStarC_Reflection_V2_Data.sort in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed
                (FStarC_Syntax_Embeddings.e_sealed
                   FStarC_Syntax_Embeddings.e_string) rng
                namedvv.FStarC_Reflection_V2_Data.ppname in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.ref_Mk_namedv_view.FStarC_Reflection_V2_Constants.t
      uu___ rng in
  let unembed_namedv_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Mk_namedv_view.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                       (fun uu___5 ->
                          fun uu___6 ->
                            fun uu___7 ->
                              {
                                FStarC_Reflection_V2_Data.uniq = uu___5;
                                FStarC_Reflection_V2_Data.sort = uu___6;
                                FStarC_Reflection_V2_Data.ppname = uu___7
                              }) FStarC_Syntax_Embeddings.e_int in
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                     uu___4 e_sort in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 e_ppname in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else FStar_Pervasives_Native.None) in
  mk_emb embed_namedv_view unembed_namedv_view
    FStarC_Reflection_V2_Constants.fstar_refl_namedv_view
let (e_bv_view :
  FStarC_Reflection_V2_Data.bv_view FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_bv_view rng bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStarC_Syntax_Embeddings.e_int rng
            bvv.FStarC_Reflection_V2_Data.index in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 = embed e_sort rng bvv.FStarC_Reflection_V2_Data.sort1 in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed
                (FStarC_Syntax_Embeddings.e_sealed
                   FStarC_Syntax_Embeddings.e_string) rng
                bvv.FStarC_Reflection_V2_Data.ppname1 in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.ref_Mk_bv_view.FStarC_Reflection_V2_Constants.t
      uu___ rng in
  let unembed_bv_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Mk_bv_view.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                       (fun uu___5 ->
                          fun uu___6 ->
                            fun uu___7 ->
                              {
                                FStarC_Reflection_V2_Data.index = uu___5;
                                FStarC_Reflection_V2_Data.sort1 = uu___6;
                                FStarC_Reflection_V2_Data.ppname1 = uu___7
                              }) FStarC_Syntax_Embeddings.e_int in
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                     uu___4 e_sort in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 e_ppname in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else FStar_Pervasives_Native.None) in
  mk_emb embed_bv_view unembed_bv_view
    FStarC_Reflection_V2_Constants.fstar_refl_bv_view
let (e_binding :
  FStarC_Reflection_V2_Data.binding FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed1 rng bindingv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed FStarC_Syntax_Embeddings.e_int rng
            bindingv.FStarC_Reflection_V2_Data.uniq1 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed e_term rng bindingv.FStarC_Reflection_V2_Data.sort3 in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed
                (FStarC_Syntax_Embeddings.e_sealed
                   FStarC_Syntax_Embeddings.e_string) rng
                bindingv.FStarC_Reflection_V2_Data.ppname3 in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.ref_Mk_binding.FStarC_Reflection_V2_Constants.t
      uu___ rng in
  let unembed t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Mk_binding.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                       (fun uu___5 ->
                          fun uu___6 ->
                            fun uu___7 ->
                              {
                                FStarC_Reflection_V2_Data.uniq1 = uu___5;
                                FStarC_Reflection_V2_Data.sort3 = uu___6;
                                FStarC_Reflection_V2_Data.ppname3 = uu___7
                              }) FStarC_Syntax_Embeddings.e_int in
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                     uu___4 e_term in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 e_ppname in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else FStar_Pervasives_Native.None) in
  mk_emb embed1 unembed FStarC_Reflection_V2_Constants.fstar_refl_binding
let (e_attribute :
  FStarC_Syntax_Syntax.attribute FStarC_Syntax_Embeddings_Base.embedding) =
  e_term
let (e_attributes :
  FStarC_Syntax_Syntax.attribute Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_attribute
let (e_binder_view :
  FStarC_Reflection_V2_Data.binder_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_binder_view rng bview =
    let uu___ =
      let uu___1 =
        let uu___2 = embed e_term rng bview.FStarC_Reflection_V2_Data.sort2 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed e_aqualv rng bview.FStarC_Reflection_V2_Data.qual in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_attributes rng bview.FStarC_Reflection_V2_Data.attrs in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed
                  (FStarC_Syntax_Embeddings.e_sealed
                     FStarC_Syntax_Embeddings.e_string) rng
                  bview.FStarC_Reflection_V2_Data.ppname2 in
              FStarC_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.ref_Mk_binder_view.FStarC_Reflection_V2_Constants.t
      uu___ rng in
  let unembed_binder_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Mk_binder_view.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                         (fun uu___6 ->
                            fun uu___7 ->
                              fun uu___8 ->
                                fun uu___9 ->
                                  {
                                    FStarC_Reflection_V2_Data.sort2 = uu___6;
                                    FStarC_Reflection_V2_Data.qual = uu___7;
                                    FStarC_Reflection_V2_Data.attrs = uu___8;
                                    FStarC_Reflection_V2_Data.ppname2 =
                                      uu___9
                                  }) e_term in
                     FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                       uu___5 e_aqualv in
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                     uu___4 (FStarC_Syntax_Embeddings.e_list e_term) in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 e_ppname in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else FStar_Pervasives_Native.None) in
  mk_emb embed_binder_view unembed_binder_view
    FStarC_Reflection_V2_Constants.fstar_refl_binder_view
let (e_comp_view :
  FStarC_Reflection_V2_Data.comp_view FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_comp_view rng cv =
    match cv with
    | FStarC_Reflection_V2_Data.C_Total t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_C_Total.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.C_GTotal t ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_term rng t in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          [uu___1] in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_C_GTotal.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
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
          FStarC_Reflection_V2_Constants.ref_C_Lemma.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.C_Eff (us, eff, res, args, decrs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              embed (FStarC_Syntax_Embeddings.e_list e_universe) rng us in
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
          FStarC_Reflection_V2_Constants.ref_C_Eff.FStarC_Reflection_V2_Constants.t
          uu___ rng in
  let unembed_comp_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_C_Total.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                   (fun uu___3 -> FStarC_Reflection_V2_Data.C_Total uu___3)
                   e_term in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_C_GTotal.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                      (fun uu___3 ->
                         FStarC_Reflection_V2_Data.C_GTotal uu___3) e_term in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_C_Lemma.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (curry3
                               (fun uu___5 ->
                                  FStarC_Reflection_V2_Data.C_Lemma uu___5))
                            e_term in
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                          uu___4 e_term in
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                        uu___3 e_term in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_C_Eff.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                  (curry5
                                     (fun uu___7 ->
                                        FStarC_Reflection_V2_Data.C_Eff
                                          uu___7))
                                  (FStarC_Syntax_Embeddings.e_list e_universe) in
                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                                uu___6 FStarC_Syntax_Embeddings.e_string_list in
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                              uu___5 e_term in
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                            uu___4 (FStarC_Syntax_Embeddings.e_list e_argv) in
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                          uu___3 (FStarC_Syntax_Embeddings.e_list e_term) in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else FStar_Pervasives_Native.None) in
  mk_emb embed_comp_view unembed_comp_view
    FStarC_Reflection_V2_Constants.fstar_refl_comp_view
let (e_univ_name :
  FStarC_Syntax_Syntax.univ_name FStarC_Syntax_Embeddings_Base.embedding) =
  e_ident
let (e_univ_names :
  FStarC_Syntax_Syntax.univ_name Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_univ_name
let (e_subst_elt :
  FStarC_Syntax_Syntax.subst_elt FStarC_Syntax_Embeddings_Base.embedding) =
  let ee rng e =
    match e with
    | FStarC_Syntax_Syntax.DB (i, x) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_fsint rng i in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_namedv rng x in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_DB.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Syntax_Syntax.DT (i, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_fsint rng i in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_term rng t in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_DT.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Syntax_Syntax.NM (x, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_namedv rng x in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed FStarC_Syntax_Embeddings.e_fsint rng i in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_NM.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Syntax_Syntax.NT (x, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_namedv rng x in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_term rng t in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_NT.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Syntax_Syntax.UN (i, u) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_fsint rng i in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed e_universe rng u in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_UN.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Syntax_Syntax.UD (u, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed e_univ_name rng u in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = embed FStarC_Syntax_Embeddings.e_fsint rng i in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_UD.FStarC_Reflection_V2_Constants.t
          uu___ rng in
  let uu t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_DB.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                     (curry (fun uu___4 -> FStarC_Syntax_Syntax.DB uu___4))
                     FStarC_Syntax_Embeddings.e_fsint in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 e_namedv in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_DT.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    let uu___3 =
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                        (curry (fun uu___4 -> FStarC_Syntax_Syntax.DT uu___4))
                        FStarC_Syntax_Embeddings.e_fsint in
                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                      uu___3 e_term in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_NM.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                          (curry
                             (fun uu___4 -> FStarC_Syntax_Syntax.NM uu___4))
                          e_namedv in
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                        uu___3 FStarC_Syntax_Embeddings.e_fsint in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_NT.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        let uu___3 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (curry
                               (fun uu___4 -> FStarC_Syntax_Syntax.NT uu___4))
                            e_namedv in
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                          uu___3 e_term in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Reflection_V2_Constants.ref_UN.FStarC_Reflection_V2_Constants.lid
                     then
                       (let uu___2 =
                          let uu___3 =
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                              (curry
                                 (fun uu___4 ->
                                    FStarC_Syntax_Syntax.UN uu___4))
                              FStarC_Syntax_Embeddings.e_fsint in
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                            uu___3 e_universe in
                        FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                     else
                       if
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Reflection_V2_Constants.ref_UD.FStarC_Reflection_V2_Constants.lid
                       then
                         (let uu___2 =
                            let uu___3 =
                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                (curry
                                   (fun uu___4 ->
                                      FStarC_Syntax_Syntax.UD uu___4))
                                e_ident in
                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                              uu___3 FStarC_Syntax_Embeddings.e_fsint in
                          FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                       else FStar_Pervasives_Native.None) in
  mk_emb ee uu FStarC_Reflection_V2_Constants.fstar_refl_subst_elt
let (e_subst :
  FStarC_Syntax_Syntax.subst_elt Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_subst_elt
let (e_ctor :
  (Prims.string Prims.list * FStarC_Syntax_Syntax.term)
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings.e_tuple2 FStarC_Syntax_Embeddings.e_string_list
    e_term
let (e_lb_view :
  FStarC_Reflection_V2_Data.lb_view FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_lb_view rng lbv =
    let uu___ =
      let uu___1 =
        let uu___2 = embed e_fv rng lbv.FStarC_Reflection_V2_Data.lb_fv in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed (FStarC_Syntax_Embeddings.e_list e_univ_name) rng
              lbv.FStarC_Reflection_V2_Data.lb_us in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_term rng lbv.FStarC_Reflection_V2_Data.lb_typ in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term rng lbv.FStarC_Reflection_V2_Data.lb_def in
              FStarC_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.ref_Mk_lb.FStarC_Reflection_V2_Constants.t
      uu___ rng in
  let unembed_lb_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Mk_lb.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                         (fun uu___6 ->
                            fun uu___7 ->
                              fun uu___8 ->
                                fun uu___9 ->
                                  {
                                    FStarC_Reflection_V2_Data.lb_fv = uu___6;
                                    FStarC_Reflection_V2_Data.lb_us = uu___7;
                                    FStarC_Reflection_V2_Data.lb_typ = uu___8;
                                    FStarC_Reflection_V2_Data.lb_def = uu___9
                                  }) e_fv in
                     FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                       uu___5 e_univ_names in
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                     uu___4 e_term in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 e_term in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else FStar_Pervasives_Native.None) in
  mk_emb embed_lb_view unembed_lb_view
    FStarC_Reflection_V2_Constants.fstar_refl_lb_view
let (e_sigelt_view :
  FStarC_Reflection_V2_Data.sigelt_view
    FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed_sigelt_view rng sev =
    match sev with
    | FStarC_Reflection_V2_Data.Sg_Let (r, lbs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_bool rng r in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStarC_Syntax_Embeddings.e_list e_letbinding) rng lbs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Sg_Let.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng nm in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStarC_Syntax_Embeddings.e_list e_univ_name) rng univs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_binders rng bs in
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
          FStarC_Reflection_V2_Constants.ref_Sg_Inductive.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Sg_Val (nm, univs, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng nm in
            FStarC_Syntax_Syntax.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                embed (FStarC_Syntax_Embeddings.e_list e_univ_name) rng univs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = embed e_term rng t in
                FStarC_Syntax_Syntax.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        FStarC_Syntax_Syntax.mk_Tm_app
          FStarC_Reflection_V2_Constants.ref_Sg_Val.FStarC_Reflection_V2_Constants.t
          uu___ rng
    | FStarC_Reflection_V2_Data.Unk ->
        let uu___ =
          FStarC_Reflection_V2_Constants.ref_Unk.FStarC_Reflection_V2_Constants.t in
        {
          FStarC_Syntax_Syntax.n = (uu___.FStarC_Syntax_Syntax.n);
          FStarC_Syntax_Syntax.pos = rng;
          FStarC_Syntax_Syntax.vars = (uu___.FStarC_Syntax_Syntax.vars);
          FStarC_Syntax_Syntax.hash_code =
            (uu___.FStarC_Syntax_Syntax.hash_code)
        } in
  let unembed_sigelt_view t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_Sg_Inductive.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                           (curry5
                              (fun uu___7 ->
                                 FStarC_Reflection_V2_Data.Sg_Inductive
                                   uu___7))
                           FStarC_Syntax_Embeddings.e_string_list in
                       FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                         uu___6 e_univ_names in
                     FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                       uu___5 e_binders in
                   FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                     uu___4 e_term in
                 FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                   uu___3 (FStarC_Syntax_Embeddings.e_list e_ctor) in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_Sg_Let.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    let uu___3 =
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                        (curry
                           (fun uu___4 ->
                              FStarC_Reflection_V2_Data.Sg_Let uu___4))
                        FStarC_Syntax_Embeddings.e_bool in
                    FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                      uu___3 (FStarC_Syntax_Embeddings.e_list e_letbinding) in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_Sg_Val.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                            (curry3
                               (fun uu___5 ->
                                  FStarC_Reflection_V2_Data.Sg_Val uu___5))
                            FStarC_Syntax_Embeddings.e_string_list in
                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                          uu___4 e_univ_names in
                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Star_Star_Greater
                        uu___3 e_term in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_Unk.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        FStarC_Syntax_Embeddings_AppEmb.pure
                          FStarC_Reflection_V2_Data.Unk in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else FStar_Pervasives_Native.None) in
  mk_emb embed_sigelt_view unembed_sigelt_view
    FStarC_Reflection_V2_Constants.fstar_refl_sigelt_view
let (e_qualifier :
  FStarC_Reflection_V2_Data.qualifier FStarC_Syntax_Embeddings_Base.embedding)
  =
  let embed1 rng q =
    let r =
      match q with
      | FStarC_Reflection_V2_Data.Assumption ->
          FStarC_Reflection_V2_Constants.ref_qual_Assumption.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.InternalAssumption ->
          FStarC_Reflection_V2_Constants.ref_qual_InternalAssumption.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.New ->
          FStarC_Reflection_V2_Constants.ref_qual_New.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Private ->
          FStarC_Reflection_V2_Constants.ref_qual_Private.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Unfold_for_unification_and_vcgen ->
          FStarC_Reflection_V2_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Visible_default ->
          FStarC_Reflection_V2_Constants.ref_qual_Visible_default.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Irreducible ->
          FStarC_Reflection_V2_Constants.ref_qual_Irreducible.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Inline_for_extraction ->
          FStarC_Reflection_V2_Constants.ref_qual_Inline_for_extraction.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.NoExtract ->
          FStarC_Reflection_V2_Constants.ref_qual_NoExtract.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Noeq ->
          FStarC_Reflection_V2_Constants.ref_qual_Noeq.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Unopteq ->
          FStarC_Reflection_V2_Constants.ref_qual_Unopteq.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.TotalEffect ->
          FStarC_Reflection_V2_Constants.ref_qual_TotalEffect.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Logic ->
          FStarC_Reflection_V2_Constants.ref_qual_Logic.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Reifiable ->
          FStarC_Reflection_V2_Constants.ref_qual_Reifiable.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.ExceptionConstructor ->
          FStarC_Reflection_V2_Constants.ref_qual_ExceptionConstructor.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.HasMaskedEffect ->
          FStarC_Reflection_V2_Constants.ref_qual_HasMaskedEffect.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Effect ->
          FStarC_Reflection_V2_Constants.ref_qual_Effect.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.OnlyName ->
          FStarC_Reflection_V2_Constants.ref_qual_OnlyName.FStarC_Reflection_V2_Constants.t
      | FStarC_Reflection_V2_Data.Reflectable l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng l in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_qual_Reflectable.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.Discriminator l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng l in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_qual_Discriminator.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.Action l ->
          let uu___ =
            let uu___1 =
              let uu___2 = embed FStarC_Syntax_Embeddings.e_string_list rng l in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_qual_Action.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.Projector (l, i) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     FStarC_Syntax_Embeddings.e_string_list e_univ_name) rng
                  (l, i) in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_qual_Projector.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.RecordType (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     (FStarC_Syntax_Embeddings.e_list e_univ_name)
                     (FStarC_Syntax_Embeddings.e_list e_univ_name)) rng
                  (ids1, ids2) in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_qual_RecordType.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange
      | FStarC_Reflection_V2_Data.RecordConstructor (ids1, ids2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                embed
                  (FStarC_Syntax_Embeddings.e_tuple2
                     (FStarC_Syntax_Embeddings.e_list e_univ_name)
                     (FStarC_Syntax_Embeddings.e_list e_univ_name)) rng
                  (ids1, ids2) in
              FStarC_Syntax_Syntax.as_arg uu___2 in
            [uu___1] in
          FStarC_Syntax_Syntax.mk_Tm_app
            FStarC_Reflection_V2_Constants.ref_qual_RecordConstructor.FStarC_Reflection_V2_Constants.t
            uu___ FStarC_Compiler_Range_Type.dummyRange in
    {
      FStarC_Syntax_Syntax.n = (r.FStarC_Syntax_Syntax.n);
      FStarC_Syntax_Syntax.pos = rng;
      FStarC_Syntax_Syntax.vars = (r.FStarC_Syntax_Syntax.vars);
      FStarC_Syntax_Syntax.hash_code = (r.FStarC_Syntax_Syntax.hash_code)
    } in
  let unembed t =
    let uu___ = head_fv_and_args t in
    FStarC_Syntax_Embeddings_AppEmb.op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (fv, args) ->
             if
               FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Reflection_V2_Constants.ref_qual_Assumption.FStarC_Reflection_V2_Constants.lid
             then
               let uu___2 =
                 FStarC_Syntax_Embeddings_AppEmb.pure
                   FStarC_Reflection_V2_Data.Assumption in
               FStarC_Syntax_Embeddings_AppEmb.run args uu___2
             else
               if
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Reflection_V2_Constants.ref_qual_InternalAssumption.FStarC_Reflection_V2_Constants.lid
               then
                 (let uu___2 =
                    FStarC_Syntax_Embeddings_AppEmb.pure
                      FStarC_Reflection_V2_Data.InternalAssumption in
                  FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
               else
                 if
                   FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Reflection_V2_Constants.ref_qual_New.FStarC_Reflection_V2_Constants.lid
                 then
                   (let uu___2 =
                      FStarC_Syntax_Embeddings_AppEmb.pure
                        FStarC_Reflection_V2_Data.New in
                    FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                 else
                   if
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Reflection_V2_Constants.ref_qual_Private.FStarC_Reflection_V2_Constants.lid
                   then
                     (let uu___2 =
                        FStarC_Syntax_Embeddings_AppEmb.pure
                          FStarC_Reflection_V2_Data.Private in
                      FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                   else
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Reflection_V2_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStarC_Reflection_V2_Constants.lid
                     then
                       (let uu___2 =
                          FStarC_Syntax_Embeddings_AppEmb.pure
                            FStarC_Reflection_V2_Data.Unfold_for_unification_and_vcgen in
                        FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                     else
                       if
                         FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Reflection_V2_Constants.ref_qual_Visible_default.FStarC_Reflection_V2_Constants.lid
                       then
                         (let uu___2 =
                            FStarC_Syntax_Embeddings_AppEmb.pure
                              FStarC_Reflection_V2_Data.Visible_default in
                          FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                       else
                         if
                           FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Reflection_V2_Constants.ref_qual_Irreducible.FStarC_Reflection_V2_Constants.lid
                         then
                           (let uu___2 =
                              FStarC_Syntax_Embeddings_AppEmb.pure
                                FStarC_Reflection_V2_Data.Irreducible in
                            FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                         else
                           if
                             FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Reflection_V2_Constants.ref_qual_Inline_for_extraction.FStarC_Reflection_V2_Constants.lid
                           then
                             (let uu___2 =
                                FStarC_Syntax_Embeddings_AppEmb.pure
                                  FStarC_Reflection_V2_Data.Inline_for_extraction in
                              FStarC_Syntax_Embeddings_AppEmb.run args uu___2)
                           else
                             if
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Reflection_V2_Constants.ref_qual_NoExtract.FStarC_Reflection_V2_Constants.lid
                             then
                               (let uu___2 =
                                  FStarC_Syntax_Embeddings_AppEmb.pure
                                    FStarC_Reflection_V2_Data.NoExtract in
                                FStarC_Syntax_Embeddings_AppEmb.run args
                                  uu___2)
                             else
                               if
                                 FStarC_Syntax_Syntax.fv_eq_lid fv
                                   FStarC_Reflection_V2_Constants.ref_qual_Noeq.FStarC_Reflection_V2_Constants.lid
                               then
                                 (let uu___2 =
                                    FStarC_Syntax_Embeddings_AppEmb.pure
                                      FStarC_Reflection_V2_Data.Noeq in
                                  FStarC_Syntax_Embeddings_AppEmb.run args
                                    uu___2)
                               else
                                 if
                                   FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Reflection_V2_Constants.ref_qual_Unopteq.FStarC_Reflection_V2_Constants.lid
                                 then
                                   (let uu___2 =
                                      FStarC_Syntax_Embeddings_AppEmb.pure
                                        FStarC_Reflection_V2_Data.Unopteq in
                                    FStarC_Syntax_Embeddings_AppEmb.run args
                                      uu___2)
                                 else
                                   if
                                     FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Reflection_V2_Constants.ref_qual_TotalEffect.FStarC_Reflection_V2_Constants.lid
                                   then
                                     (let uu___2 =
                                        FStarC_Syntax_Embeddings_AppEmb.pure
                                          FStarC_Reflection_V2_Data.TotalEffect in
                                      FStarC_Syntax_Embeddings_AppEmb.run
                                        args uu___2)
                                   else
                                     if
                                       FStarC_Syntax_Syntax.fv_eq_lid fv
                                         FStarC_Reflection_V2_Constants.ref_qual_Logic.FStarC_Reflection_V2_Constants.lid
                                     then
                                       (let uu___2 =
                                          FStarC_Syntax_Embeddings_AppEmb.pure
                                            FStarC_Reflection_V2_Data.Logic in
                                        FStarC_Syntax_Embeddings_AppEmb.run
                                          args uu___2)
                                     else
                                       if
                                         FStarC_Syntax_Syntax.fv_eq_lid fv
                                           FStarC_Reflection_V2_Constants.ref_qual_Reifiable.FStarC_Reflection_V2_Constants.lid
                                       then
                                         (let uu___2 =
                                            FStarC_Syntax_Embeddings_AppEmb.pure
                                              FStarC_Reflection_V2_Data.Reifiable in
                                          FStarC_Syntax_Embeddings_AppEmb.run
                                            args uu___2)
                                       else
                                         if
                                           FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Reflection_V2_Constants.ref_qual_ExceptionConstructor.FStarC_Reflection_V2_Constants.lid
                                         then
                                           (let uu___2 =
                                              FStarC_Syntax_Embeddings_AppEmb.pure
                                                FStarC_Reflection_V2_Data.ExceptionConstructor in
                                            FStarC_Syntax_Embeddings_AppEmb.run
                                              args uu___2)
                                         else
                                           if
                                             FStarC_Syntax_Syntax.fv_eq_lid
                                               fv
                                               FStarC_Reflection_V2_Constants.ref_qual_HasMaskedEffect.FStarC_Reflection_V2_Constants.lid
                                           then
                                             (let uu___2 =
                                                FStarC_Syntax_Embeddings_AppEmb.pure
                                                  FStarC_Reflection_V2_Data.HasMaskedEffect in
                                              FStarC_Syntax_Embeddings_AppEmb.run
                                                args uu___2)
                                           else
                                             if
                                               FStarC_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStarC_Reflection_V2_Constants.ref_qual_Effect.FStarC_Reflection_V2_Constants.lid
                                             then
                                               (let uu___2 =
                                                  FStarC_Syntax_Embeddings_AppEmb.pure
                                                    FStarC_Reflection_V2_Data.Effect in
                                                FStarC_Syntax_Embeddings_AppEmb.run
                                                  args uu___2)
                                             else
                                               if
                                                 FStarC_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStarC_Reflection_V2_Constants.ref_qual_OnlyName.FStarC_Reflection_V2_Constants.lid
                                               then
                                                 (let uu___2 =
                                                    FStarC_Syntax_Embeddings_AppEmb.pure
                                                      FStarC_Reflection_V2_Data.OnlyName in
                                                  FStarC_Syntax_Embeddings_AppEmb.run
                                                    args uu___2)
                                               else
                                                 if
                                                   FStarC_Syntax_Syntax.fv_eq_lid
                                                     fv
                                                     FStarC_Reflection_V2_Constants.ref_qual_Reflectable.FStarC_Reflection_V2_Constants.lid
                                                 then
                                                   (let uu___2 =
                                                      FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                        (fun uu___3 ->
                                                           FStarC_Reflection_V2_Data.Reflectable
                                                             uu___3) e_name in
                                                    FStarC_Syntax_Embeddings_AppEmb.run
                                                      args uu___2)
                                                 else
                                                   if
                                                     FStarC_Syntax_Syntax.fv_eq_lid
                                                       fv
                                                       FStarC_Reflection_V2_Constants.ref_qual_Discriminator.FStarC_Reflection_V2_Constants.lid
                                                   then
                                                     (let uu___2 =
                                                        FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                          (fun uu___3 ->
                                                             FStarC_Reflection_V2_Data.Discriminator
                                                               uu___3) e_name in
                                                      FStarC_Syntax_Embeddings_AppEmb.run
                                                        args uu___2)
                                                   else
                                                     if
                                                       FStarC_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStarC_Reflection_V2_Constants.ref_qual_Action.FStarC_Reflection_V2_Constants.lid
                                                     then
                                                       (let uu___2 =
                                                          FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                            (fun uu___3 ->
                                                               FStarC_Reflection_V2_Data.Action
                                                                 uu___3)
                                                            e_name in
                                                        FStarC_Syntax_Embeddings_AppEmb.run
                                                          args uu___2)
                                                     else
                                                       if
                                                         FStarC_Syntax_Syntax.fv_eq_lid
                                                           fv
                                                           FStarC_Reflection_V2_Constants.ref_qual_Projector.FStarC_Reflection_V2_Constants.lid
                                                       then
                                                         (let uu___2 =
                                                            FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                              (fun uu___3 ->
                                                                 FStarC_Reflection_V2_Data.Projector
                                                                   uu___3)
                                                              (FStarC_Syntax_Embeddings.e_tuple2
                                                                 e_name
                                                                 e_ident) in
                                                          FStarC_Syntax_Embeddings_AppEmb.run
                                                            args uu___2)
                                                       else
                                                         if
                                                           FStarC_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStarC_Reflection_V2_Constants.ref_qual_RecordType.FStarC_Reflection_V2_Constants.lid
                                                         then
                                                           (let uu___2 =
                                                              FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                                (fun uu___3
                                                                   ->
                                                                   FStarC_Reflection_V2_Data.RecordType
                                                                    uu___3)
                                                                (FStarC_Syntax_Embeddings.e_tuple2
                                                                   (FStarC_Syntax_Embeddings.e_list
                                                                    e_ident)
                                                                   (FStarC_Syntax_Embeddings.e_list
                                                                    e_ident)) in
                                                            FStarC_Syntax_Embeddings_AppEmb.run
                                                              args uu___2)
                                                         else
                                                           if
                                                             FStarC_Syntax_Syntax.fv_eq_lid
                                                               fv
                                                               FStarC_Reflection_V2_Constants.ref_qual_RecordConstructor.FStarC_Reflection_V2_Constants.lid
                                                           then
                                                             (let uu___2 =
                                                                FStarC_Syntax_Embeddings_AppEmb.op_Less_Dollar_Dollar_Greater
                                                                  (fun uu___3
                                                                    ->
                                                                    FStarC_Reflection_V2_Data.RecordConstructor
                                                                    uu___3)
                                                                  (FStarC_Syntax_Embeddings.e_tuple2
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    e_ident)
                                                                    (FStarC_Syntax_Embeddings.e_list
                                                                    e_ident)) in
                                                              FStarC_Syntax_Embeddings_AppEmb.run
                                                                args uu___2)
                                                           else
                                                             FStar_Pervasives_Native.None) in
  mk_emb embed1 unembed FStarC_Reflection_V2_Constants.fstar_refl_qualifier
let (e_qualifiers :
  FStarC_Reflection_V2_Data.qualifier Prims.list
    FStarC_Syntax_Embeddings_Base.embedding)
  = FStarC_Syntax_Embeddings.e_list e_qualifier
let (unfold_lazy_bv :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let bv = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_bv bv in
          embed e_bv_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_bv.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_namedv :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let namedv1 = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_namedv namedv1 in
          embed e_namedv_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_namedv.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_binder :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let binder = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_binder binder in
          embed e_binder_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_binder.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_letbinding :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let lb = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let lbv = FStarC_Reflection_V2_Builtins.inspect_lb lb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          embed e_fv i.FStarC_Syntax_Syntax.rng
            lbv.FStarC_Reflection_V2_Data.lb_fv in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            embed (FStarC_Syntax_Embeddings.e_list e_univ_name)
              i.FStarC_Syntax_Syntax.rng lbv.FStarC_Reflection_V2_Data.lb_us in
          FStarC_Syntax_Syntax.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              embed e_term i.FStarC_Syntax_Syntax.rng
                lbv.FStarC_Reflection_V2_Data.lb_typ in
            FStarC_Syntax_Syntax.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                embed e_term i.FStarC_Syntax_Syntax.rng
                  lbv.FStarC_Reflection_V2_Data.lb_def in
              FStarC_Syntax_Syntax.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_lb.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_fvar :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let fv = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_fv fv in
          embed FStarC_Syntax_Embeddings.e_string_list
            i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_fv.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_comp :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let comp = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_comp comp in
          embed e_comp_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_comp.FStarC_Reflection_V2_Constants.t
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
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_sigelt sigelt in
          embed e_sigelt_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_sigelt.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_universe :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let u = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Reflection_V2_Builtins.inspect_universe u in
          embed e_universe_view i.FStarC_Syntax_Syntax.rng uu___3 in
        FStarC_Syntax_Syntax.as_arg uu___2 in
      [uu___1] in
    FStarC_Syntax_Syntax.mk_Tm_app
      FStarC_Reflection_V2_Constants.fstar_refl_pack_universe.FStarC_Reflection_V2_Constants.t
      uu___ i.FStarC_Syntax_Syntax.rng
let (unfold_lazy_doc :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term) =
  fun i ->
    let d = FStarC_Dyn.undyn i.FStarC_Syntax_Syntax.blob in
    let lid = FStarC_Ident.lid_of_str "FStar.Stubs.Pprint.arbitrary_string" in
    let s = FStarC_Pprint.render d in
    let uu___ = FStarC_Syntax_Syntax.fvar lid FStar_Pervasives_Native.None in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          embed FStarC_Syntax_Embeddings.e_string i.FStarC_Syntax_Syntax.rng
            s in
        FStarC_Syntax_Syntax.as_arg uu___3 in
      [uu___2] in
    FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 i.FStarC_Syntax_Syntax.rng