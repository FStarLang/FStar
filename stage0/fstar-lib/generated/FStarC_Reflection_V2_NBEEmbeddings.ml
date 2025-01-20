open Prims
let (noaqs : FStarC_Syntax_Syntax.antiquotations) = (Prims.int_zero, [])
let (mkFV :
  FStarC_Syntax_Syntax.fv ->
    FStarC_Syntax_Syntax.universe Prims.list ->
      (FStarC_TypeChecker_NBETerm.t * FStarC_Syntax_Syntax.aqual) Prims.list
        -> FStarC_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStarC_TypeChecker_NBETerm.mkFV fv (FStarC_Compiler_List.rev us)
          (FStarC_Compiler_List.rev ts)
let (mkConstruct :
  FStarC_Syntax_Syntax.fv ->
    FStarC_Syntax_Syntax.universe Prims.list ->
      (FStarC_TypeChecker_NBETerm.t * FStarC_Syntax_Syntax.aqual) Prims.list
        -> FStarC_TypeChecker_NBETerm.t)
  =
  fun fv ->
    fun us ->
      fun ts ->
        FStarC_TypeChecker_NBETerm.mkConstruct fv
          (FStarC_Compiler_List.rev us) (FStarC_Compiler_List.rev ts)
let (fv_as_emb_typ : FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.emb_typ)
  =
  fun fv ->
    let uu___ =
      let uu___1 =
        FStarC_Ident.string_of_lid
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___
let mk_emb' :
  'uuuuu .
    (FStarC_TypeChecker_NBETerm.nbe_cbs ->
       'uuuuu -> FStarC_TypeChecker_NBETerm.t)
      ->
      (FStarC_TypeChecker_NBETerm.nbe_cbs ->
         FStarC_TypeChecker_NBETerm.t ->
           'uuuuu FStar_Pervasives_Native.option)
        ->
        FStarC_Syntax_Syntax.fv ->
          'uuuuu FStarC_TypeChecker_NBETerm.embedding
  =
  fun x ->
    fun y ->
      fun fv ->
        FStarC_TypeChecker_NBETerm.mk_emb x y (fun uu___ -> mkFV fv [] [])
          (fun uu___ -> fv_as_emb_typ fv)
let mk_lazy :
  'uuuuu .
    FStarC_TypeChecker_NBETerm.nbe_cbs ->
      'uuuuu ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          FStarC_Syntax_Syntax.lazy_kind -> FStarC_TypeChecker_NBETerm.t
  =
  fun cb ->
    fun obj ->
      fun ty ->
        fun kind ->
          let li =
            let uu___ = FStarC_Dyn.mkdyn obj in
            {
              FStarC_Syntax_Syntax.blob = uu___;
              FStarC_Syntax_Syntax.lkind = kind;
              FStarC_Syntax_Syntax.ltyp = ty;
              FStarC_Syntax_Syntax.rng =
                FStarC_Compiler_Range_Type.dummyRange
            } in
          let thunk =
            FStarC_Thunk.mk
              (fun uu___ ->
                 let uu___1 = FStarC_Syntax_Util.unfold_lazy li in
                 FStarC_TypeChecker_NBETerm.translate_cb cb uu___1) in
          FStarC_TypeChecker_NBETerm.mk_t
            (FStarC_TypeChecker_NBETerm.Lazy
               ((FStar_Pervasives.Inl li), thunk))
let (e_bv : FStarC_Syntax_Syntax.bv FStarC_TypeChecker_NBETerm.embedding) =
  let embed_bv cb bv =
    mk_lazy cb bv FStarC_Reflection_V2_Constants.fstar_refl_bv
      FStarC_Syntax_Syntax.Lazy_bv in
  let unembed_bv cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_bv;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded bv: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv unembed_bv FStarC_Reflection_V2_Constants.fstar_refl_bv_fv
let (e_namedv :
  FStarC_Reflection_V2_Data.namedv FStarC_TypeChecker_NBETerm.embedding) =
  let embed_namedv cb namedv =
    mk_lazy cb namedv FStarC_Reflection_V2_Constants.fstar_refl_namedv
      FStarC_Syntax_Syntax.Lazy_namedv in
  let unembed_namedv cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_namedv;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded namedv: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_namedv unembed_namedv
    FStarC_Reflection_V2_Constants.fstar_refl_namedv_fv
let (e_binder :
  FStarC_Syntax_Syntax.binder FStarC_TypeChecker_NBETerm.embedding) =
  let embed_binder cb b =
    mk_lazy cb b FStarC_Reflection_V2_Constants.fstar_refl_binder
      FStarC_Syntax_Syntax.Lazy_binder in
  let unembed_binder cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_binder;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded binder: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_binder unembed_binder
    FStarC_Reflection_V2_Constants.fstar_refl_binder_fv
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
  (Prims.int * FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    Prims.list) ->
    FStarC_Syntax_Syntax.term FStarC_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let embed_term cb t =
      let qi =
        {
          FStarC_Syntax_Syntax.qkind = FStarC_Syntax_Syntax.Quote_static;
          FStarC_Syntax_Syntax.antiquotations = aq
        } in
      FStarC_TypeChecker_NBETerm.mk_t
        (FStarC_TypeChecker_NBETerm.Quote (t, qi)) in
    let unembed_term cb t =
      match t.FStarC_TypeChecker_NBETerm.nbe_t with
      | FStarC_TypeChecker_NBETerm.Quote (tm, qi) ->
          let uu___ =
            FStarC_Reflection_V2_Embeddings.e_term_aq (Prims.int_zero, []) in
          let uu___1 =
            FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_quoted (tm, qi))
              FStarC_Compiler_Range_Type.dummyRange in
          FStarC_Syntax_Embeddings_Base.unembed uu___ uu___1
            FStarC_Syntax_Embeddings_Base.id_norm_cb
      | uu___ -> FStar_Pervasives_Native.None in
    {
      FStarC_TypeChecker_NBETerm.em = embed_term;
      FStarC_TypeChecker_NBETerm.un = unembed_term;
      FStarC_TypeChecker_NBETerm.typ =
        (fun uu___ ->
           mkFV FStarC_Reflection_V2_Constants.fstar_refl_term_fv [] []);
      FStarC_TypeChecker_NBETerm.e_typ =
        (fun uu___ ->
           fv_as_emb_typ FStarC_Reflection_V2_Constants.fstar_refl_term_fv)
    }
let (e_term : FStarC_Syntax_Syntax.term FStarC_TypeChecker_NBETerm.embedding)
  = e_term_aq (Prims.int_zero, [])
let (e_sort :
  FStarC_Syntax_Syntax.term FStarC_Compiler_Sealed.sealed
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_sealed e_term
let (e_ppname :
  Prims.string FStarC_Compiler_Sealed.sealed
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_sealed FStarC_TypeChecker_NBETerm.e_string
let (e_aqualv :
  FStarC_Reflection_V2_Data.aqualv FStarC_TypeChecker_NBETerm.embedding) =
  let embed_aqualv cb q =
    match q with
    | FStarC_Reflection_V2_Data.Q_Explicit ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Q_Explicit.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Q_Implicit ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Q_Implicit.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Q_Meta t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_term cb t in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Q_Meta.FStarC_Reflection_V2_Constants.fv
          [] uu___ in
  let unembed_aqualv cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Q_Explicit.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Q_Explicit
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Q_Implicit.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Q_Implicit
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (t1, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Q_Meta.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun t2 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Q_Meta t2))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded aqualv: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  FStarC_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv
    (fun uu___ ->
       mkConstruct FStarC_Reflection_V2_Constants.fstar_refl_aqualv_fv [] [])
    (fun uu___ ->
       fv_as_emb_typ FStarC_Reflection_V2_Constants.fstar_refl_aqualv_fv)
let (e_binders :
  FStarC_Syntax_Syntax.binders FStarC_TypeChecker_NBETerm.embedding) =
  FStarC_TypeChecker_NBETerm.e_list e_binder
let (e_fv : FStarC_Syntax_Syntax.fv FStarC_TypeChecker_NBETerm.embedding) =
  let embed_fv cb fv =
    mk_lazy cb fv FStarC_Reflection_V2_Constants.fstar_refl_fv
      FStarC_Syntax_Syntax.Lazy_fvar in
  let unembed_fv cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_fvar;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded fvar: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_fv unembed_fv FStarC_Reflection_V2_Constants.fstar_refl_fv_fv
let (e_comp : FStarC_Syntax_Syntax.comp FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_comp cb c =
    mk_lazy cb c FStarC_Reflection_V2_Constants.fstar_refl_comp
      FStarC_Syntax_Syntax.Lazy_comp in
  let unembed_comp cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_comp;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded comp: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_comp unembed_comp
    FStarC_Reflection_V2_Constants.fstar_refl_comp_fv
let (e_env : FStarC_TypeChecker_Env.env FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_env cb e =
    mk_lazy cb e FStarC_Reflection_V2_Constants.fstar_refl_env
      FStarC_Syntax_Syntax.Lazy_env in
  let unembed_env cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_env;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded env: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_env unembed_env
    FStarC_Reflection_V2_Constants.fstar_refl_env_fv
let (e_vconst :
  FStarC_Reflection_V2_Data.vconst FStarC_TypeChecker_NBETerm.embedding) =
  let embed_const cb c =
    match c with
    | FStarC_Reflection_V2_Data.C_Unit ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Unit.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.C_True ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_True.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.C_False ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_False.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.C_Int i ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.mk_t
                (FStarC_TypeChecker_NBETerm.Constant
                   (FStarC_TypeChecker_NBETerm.Int i)) in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Int.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.C_String s ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_string cb s in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_String.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.C_Range r ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_range cb r in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Range.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.C_Reify ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Reify.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.C_Reflect ns ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_string_list cb ns in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Reflect.FStarC_Reflection_V2_Constants.fv
          [] uu___ in
  let unembed_const cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Unit.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.C_Unit
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_True.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.C_True
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_False.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.C_False
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (i, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Int.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb i in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun i1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.C_Int i1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (s, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_String.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed
            FStarC_TypeChecker_NBETerm.e_string cb s in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun s1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.C_String s1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (r, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Range.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed
            FStarC_TypeChecker_NBETerm.e_range cb r in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun r1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.C_Range r1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Reify.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.C_Reify
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (ns, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Reflect.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed
            FStarC_TypeChecker_NBETerm.e_string_list cb ns in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun ns1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.C_Reflect ns1))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded vconst: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_const unembed_const
    FStarC_Reflection_V2_Constants.fstar_refl_vconst_fv
let (e_universe :
  FStarC_Syntax_Syntax.universe FStarC_TypeChecker_NBETerm.embedding) =
  let embed_universe cb u =
    mk_lazy cb u FStarC_Reflection_V2_Constants.fstar_refl_universe
      FStarC_Syntax_Syntax.Lazy_universe in
  let unembed_universe cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_universe;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded universe: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_universe unembed_universe
    FStarC_Reflection_V2_Constants.fstar_refl_universe_fv
let rec e_pattern_aq :
  'uuuuu .
    'uuuuu ->
      FStarC_Reflection_V2_Data.pattern FStarC_TypeChecker_NBETerm.embedding
  =
  fun aq ->
    let embed_pattern cb p =
      match p with
      | FStarC_Reflection_V2_Data.Pat_Constant c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_vconst cb c in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Pat_Constant.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Pat_Cons (fv, us_opt, ps) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_fv cb fv in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed
                    (FStarC_TypeChecker_NBETerm.e_option
                       (FStarC_TypeChecker_NBETerm.e_list e_universe)) cb
                    us_opt in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = e_pattern_aq aq in
                        FStarC_TypeChecker_NBETerm.e_tuple2 uu___9
                          FStarC_TypeChecker_NBETerm.e_bool in
                      FStarC_TypeChecker_NBETerm.e_list uu___8 in
                    FStarC_TypeChecker_NBETerm.embed uu___7 cb ps in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Pat_Cons.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Pat_Var (sort, ppname) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_sort cb sort in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed e_ppname cb ppname in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Pat_Var.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Pat_Dot_Term eopt ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed
                  (FStarC_TypeChecker_NBETerm.e_option e_term) cb eopt in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Pat_Dot_Term.FStarC_Reflection_V2_Constants.fv
            [] uu___ in
    let unembed_pattern cb t =
      match t.FStarC_TypeChecker_NBETerm.nbe_t with
      | FStarC_TypeChecker_NBETerm.Construct (fv, [], (c, uu___)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Pat_Constant.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___1 = FStarC_TypeChecker_NBETerm.unembed e_vconst cb c in
          FStarC_Compiler_Util.bind_opt uu___1
            (fun c1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Pat_Constant c1))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, [], (ps, uu___)::(us_opt, uu___1)::(f, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Pat_Cons.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_fv cb f in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun f1 ->
               let uu___4 =
                 FStarC_TypeChecker_NBETerm.unembed
                   (FStarC_TypeChecker_NBETerm.e_option
                      (FStarC_TypeChecker_NBETerm.e_list e_universe)) cb
                   us_opt in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun us ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = e_pattern_aq aq in
                          FStarC_TypeChecker_NBETerm.e_tuple2 uu___8
                            FStarC_TypeChecker_NBETerm.e_bool in
                        FStarC_TypeChecker_NBETerm.e_list uu___7 in
                      FStarC_TypeChecker_NBETerm.unembed uu___6 cb ps in
                    FStarC_Compiler_Util.bind_opt uu___5
                      (fun ps1 ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V2_Data.Pat_Cons (f1, us, ps1)))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, [], (ppname, uu___)::(sort, uu___1)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Pat_Var.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_sort cb sort in
          FStarC_Compiler_Util.bind_opt uu___2
            (fun sort1 ->
               let uu___3 =
                 FStarC_TypeChecker_NBETerm.unembed e_ppname cb ppname in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun ppname1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V2_Data.Pat_Var (sort1, ppname1))))
      | FStarC_TypeChecker_NBETerm.Construct (fv, [], (eopt, uu___)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Pat_Dot_Term.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___1 =
            FStarC_TypeChecker_NBETerm.unembed
              (FStarC_TypeChecker_NBETerm.e_option e_term) cb eopt in
          FStarC_Compiler_Util.bind_opt uu___1
            (fun eopt1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Pat_Dot_Term eopt1))
      | uu___ ->
          ((let uu___2 =
              let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded pattern: %s"
                uu___3 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2));
           FStar_Pervasives_Native.None) in
    mk_emb' embed_pattern unembed_pattern
      FStarC_Reflection_V2_Constants.fstar_refl_pattern_fv
let (e_pattern :
  FStarC_Reflection_V2_Data.pattern FStarC_TypeChecker_NBETerm.embedding) =
  e_pattern_aq noaqs
let (e_branch :
  FStarC_Reflection_V2_Data.branch FStarC_TypeChecker_NBETerm.embedding) =
  FStarC_TypeChecker_NBETerm.e_tuple2 e_pattern e_term
let (e_argv :
  FStarC_Reflection_V2_Data.argv FStarC_TypeChecker_NBETerm.embedding) =
  FStarC_TypeChecker_NBETerm.e_tuple2 e_term e_aqualv
let (e_branch_aq :
  (Prims.int * FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    Prims.list) ->
    (FStarC_Reflection_V2_Data.pattern * FStarC_Syntax_Syntax.term)
      FStarC_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let uu___ = e_pattern_aq aq in
    FStarC_TypeChecker_NBETerm.e_tuple2 uu___ (e_term_aq aq)
let (e_argv_aq :
  (Prims.int * FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    Prims.list) ->
    (FStarC_Syntax_Syntax.term * FStarC_Reflection_V2_Data.aqualv)
      FStarC_TypeChecker_NBETerm.embedding)
  = fun aq -> FStarC_TypeChecker_NBETerm.e_tuple2 (e_term_aq aq) e_aqualv
let (e_match_returns_annotation :
  (FStarC_Syntax_Syntax.binder * ((FStarC_Syntax_Syntax.term,
    FStarC_Syntax_Syntax.comp) FStar_Pervasives.either *
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
    FStar_Pervasives_Native.option FStarC_TypeChecker_NBETerm.embedding)
  =
  FStarC_TypeChecker_NBETerm.e_option
    (FStarC_TypeChecker_NBETerm.e_tuple2 e_binder
       (FStarC_TypeChecker_NBETerm.e_tuple3
          (FStarC_TypeChecker_NBETerm.e_either e_term e_comp)
          (FStarC_TypeChecker_NBETerm.e_option e_term)
          FStarC_TypeChecker_NBETerm.e_bool))
let unlazy_as_t :
  'uuuuu .
    FStarC_Syntax_Syntax.lazy_kind -> FStarC_TypeChecker_NBETerm.t -> 'uuuuu
  =
  fun k ->
    fun t ->
      match t.FStarC_TypeChecker_NBETerm.nbe_t with
      | FStarC_TypeChecker_NBETerm.Lazy
          (FStar_Pervasives.Inl
           { FStarC_Syntax_Syntax.blob = v; FStarC_Syntax_Syntax.lkind = k';
             FStarC_Syntax_Syntax.ltyp = uu___;
             FStarC_Syntax_Syntax.rng = uu___1;_},
           uu___2)
          when
          FStarC_Class_Deq.op_Equals_Question
            FStarC_Syntax_Syntax.deq_lazy_kind k k'
          -> FStarC_Dyn.undyn v
      | uu___ -> failwith "Not a Lazy of the expected kind (NBE)"
let (e_ident : FStarC_Ident.ident FStarC_TypeChecker_NBETerm.embedding) =
  let embed_ident cb se =
    mk_lazy cb se FStarC_Reflection_V2_Constants.fstar_refl_ident
      FStarC_Syntax_Syntax.Lazy_ident in
  let unembed_ident cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_ident;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded ident: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_ident unembed_ident
    FStarC_Reflection_V2_Constants.fstar_refl_ident_fv
let (e_univ_name :
  FStarC_Syntax_Syntax.univ_name FStarC_TypeChecker_NBETerm.embedding) =
  e_ident
let (e_univ_names :
  FStarC_Syntax_Syntax.univ_name Prims.list
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_list e_univ_name
let (e_universe_view :
  FStarC_Reflection_V2_Data.universe_view
    FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_universe_view cb uv =
    match uv with
    | FStarC_Reflection_V2_Data.Uv_Zero ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_Zero.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Uv_Succ u ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_universe cb u in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_Succ.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Uv_Max us ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                (FStarC_TypeChecker_NBETerm.e_list e_universe) cb us in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_Max.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Uv_BVar n ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_int cb n in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_BVar.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Uv_Name i ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_ident cb i in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_Name.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Uv_Unif u ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              mk_lazy cb u FStarC_Syntax_Util.t_universe_uvar
                FStarC_Syntax_Syntax.Lazy_universe_uvar in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_Unif.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Uv_Unk ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Uv_Unk.FStarC_Reflection_V2_Constants.fv
          [] [] in
  let unembed_universe_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_Zero.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Uv_Zero
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (u, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_Succ.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_universe cb u in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun u1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Uv_Succ u1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (us, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_Max.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 =
          FStarC_TypeChecker_NBETerm.unembed
            (FStarC_TypeChecker_NBETerm.e_list e_universe) cb us in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun us1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Uv_Max us1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (n, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_BVar.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb n in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun n1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Uv_BVar n1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (i, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_Name.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_ident cb i in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun i1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Uv_Name i1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (u, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_Unif.FStarC_Reflection_V2_Constants.lid
        ->
        let u1 = unlazy_as_t FStarC_Syntax_Syntax.Lazy_universe_uvar u in
        FStar_Pervasives_Native.Some (FStarC_Reflection_V2_Data.Uv_Unif u1)
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Uv_Unk.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Uv_Unk
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded universe view: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_universe_view unembed_universe_view
    FStarC_Reflection_V2_Constants.fstar_refl_universe_view_fv
let (e_subst_elt :
  FStarC_Syntax_Syntax.subst_elt FStarC_TypeChecker_NBETerm.embedding) =
  let embed_const cb e =
    match e with
    | FStarC_Syntax_Syntax.DB (i, x) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_BigInt.of_int_fs i in
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_int cb uu___3 in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_TypeChecker_NBETerm.embed e_namedv cb x in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_DB.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Syntax_Syntax.NM (x, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_namedv cb x in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_BigInt.of_int_fs i in
                FStarC_TypeChecker_NBETerm.embed
                  FStarC_TypeChecker_NBETerm.e_int cb uu___5 in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_NM.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Syntax_Syntax.NT (x, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_namedv cb x in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_TypeChecker_NBETerm.embed e_term cb t in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_NT.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Syntax_Syntax.UN (i, u) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_BigInt.of_int_fs i in
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_int cb uu___3 in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_TypeChecker_NBETerm.embed e_universe cb u in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_UN.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Syntax_Syntax.UD (n, i) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_univ_name cb n in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_BigInt.of_int_fs i in
                FStarC_TypeChecker_NBETerm.embed
                  FStarC_TypeChecker_NBETerm.e_int cb uu___5 in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_UD.FStarC_Reflection_V2_Constants.fv
          [] uu___ in
  let unembed_const cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, [], (x, uu___)::(i, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_DB.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb i in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun i1 ->
             let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_namedv cb x in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun x1 ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_BigInt.to_int_fs i1 in (uu___6, x1) in
                    FStarC_Syntax_Syntax.DB uu___5 in
                  FStar_Pervasives_Native.Some uu___4))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, [], (i, uu___)::(x, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_NM.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_namedv cb x in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun x1 ->
             let uu___3 =
               FStarC_TypeChecker_NBETerm.unembed
                 FStarC_TypeChecker_NBETerm.e_int cb i in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_BigInt.to_int_fs i1 in (x1, uu___6) in
                    FStarC_Syntax_Syntax.NM uu___5 in
                  FStar_Pervasives_Native.Some uu___4))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, [], (t1, uu___)::(x, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_NT.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_namedv cb x in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun x1 ->
             let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun t2 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Syntax_Syntax.NT (x1, t2))))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, [], (u, uu___)::(i, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_UN.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb i in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun i1 ->
             let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_universe cb u in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun u1 ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_BigInt.to_int_fs i1 in (uu___6, u1) in
                    FStarC_Syntax_Syntax.UN uu___5 in
                  FStar_Pervasives_Native.Some uu___4))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, [], (i, uu___)::(n, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_UD.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_univ_name cb n in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun n1 ->
             let uu___3 =
               FStarC_TypeChecker_NBETerm.unembed
                 FStarC_TypeChecker_NBETerm.e_int cb i in
             FStarC_Compiler_Util.bind_opt uu___3
               (fun i1 ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_BigInt.to_int_fs i1 in (n1, uu___6) in
                    FStarC_Syntax_Syntax.UD uu___5 in
                  FStar_Pervasives_Native.Some uu___4))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded vconst: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_const unembed_const
    FStarC_Reflection_V2_Constants.fstar_refl_subst_elt_fv
let (e_subst :
  FStarC_Syntax_Syntax.subst_elt Prims.list
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_list e_subst_elt
let (e_term_view_aq :
  (Prims.int * FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    Prims.list) ->
    FStarC_Reflection_V2_Data.term_view FStarC_TypeChecker_NBETerm.embedding)
  =
  fun aq ->
    let shift uu___ =
      match uu___ with | (s, aqs) -> ((s + Prims.int_one), aqs) in
    let embed_term_view cb tv =
      match tv with
      | FStarC_Reflection_V2_Data.Tv_FVar fv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_fv cb fv in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_FVar.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_BVar bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_bv cb bv in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_BVar.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Var bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_bv cb bv in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Var.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_fv cb fv in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed
                    (FStarC_TypeChecker_NBETerm.e_list e_universe) cb us in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_UInst.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_App (hd, a) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed (e_term_aq aq) cb hd in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed (e_argv_aq aq) cb a in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_App.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Abs (b, t) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_binder cb b in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed (e_term_aq (shift aq)) cb
                    t in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Abs.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_binder cb b in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_TypeChecker_NBETerm.embed e_comp cb c in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Arrow.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Type u ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_universe cb u in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Type.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Refine (b, t) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_binder cb b in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed (e_term_aq (shift aq)) cb
                    t in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Refine.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_NBETerm.embed e_vconst cb c in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            [uu___1] in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Const.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Uvar (u, d) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed
                  FStarC_TypeChecker_NBETerm.e_int cb u in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  mk_lazy cb (u, d) FStarC_Syntax_Util.t_ctx_uvar_and_sust
                    FStarC_Syntax_Syntax.Lazy_uvar in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Uvar.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Let (r, attrs, b, t1, t2) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed
                  FStarC_TypeChecker_NBETerm.e_bool cb r in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed
                    (FStarC_TypeChecker_NBETerm.e_list e_term) cb attrs in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStarC_TypeChecker_NBETerm.embed e_binder cb b in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_TypeChecker_NBETerm.embed (e_term_aq aq) cb t1 in
                    FStarC_TypeChecker_NBETerm.as_arg uu___8 in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        FStarC_TypeChecker_NBETerm.embed
                          (e_term_aq (shift aq)) cb t2 in
                      FStarC_TypeChecker_NBETerm.as_arg uu___10 in
                    [uu___9] in
                  uu___7 :: uu___8 in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Let.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Match (t, ret_opt, brs) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed (e_term_aq aq) cb t in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed e_match_returns_annotation
                    cb ret_opt in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = e_branch_aq aq in
                      FStarC_TypeChecker_NBETerm.e_list uu___8 in
                    FStarC_TypeChecker_NBETerm.embed uu___7 cb brs in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Match.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_AscribedT (e, t, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed (e_term_aq aq) cb e in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_NBETerm.embed (e_term_aq aq) cb t in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.embed
                      (FStarC_TypeChecker_NBETerm.e_option (e_term_aq aq)) cb
                      tacopt in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_TypeChecker_NBETerm.embed
                        FStarC_TypeChecker_NBETerm.e_bool cb use_eq in
                    FStarC_TypeChecker_NBETerm.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_AscT.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_TypeChecker_NBETerm.embed (e_term_aq aq) cb e in
              FStarC_TypeChecker_NBETerm.as_arg uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_TypeChecker_NBETerm.embed e_comp cb c in
                FStarC_TypeChecker_NBETerm.as_arg uu___4 in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.embed
                      (FStarC_TypeChecker_NBETerm.e_option (e_term_aq aq)) cb
                      tacopt in
                  FStarC_TypeChecker_NBETerm.as_arg uu___6 in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_TypeChecker_NBETerm.embed
                        FStarC_TypeChecker_NBETerm.e_bool cb use_eq in
                    FStarC_TypeChecker_NBETerm.as_arg uu___8 in
                  [uu___7] in
                uu___5 :: uu___6 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_AscT.FStarC_Reflection_V2_Constants.fv
            [] uu___
      | FStarC_Reflection_V2_Data.Tv_Unknown ->
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Unknown.FStarC_Reflection_V2_Constants.fv
            [] []
      | FStarC_Reflection_V2_Data.Tv_Unsupp ->
          mkConstruct
            FStarC_Reflection_V2_Constants.ref_Tv_Unsupp.FStarC_Reflection_V2_Constants.fv
            [] [] in
    let unembed_term_view cb t =
      match t.FStarC_TypeChecker_NBETerm.nbe_t with
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (b, uu___1)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Var.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_bv cb b in
          FStarC_Compiler_Util.bind_opt uu___2
            (fun b1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Tv_Var b1))
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (b, uu___1)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_BVar.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_bv cb b in
          FStarC_Compiler_Util.bind_opt uu___2
            (fun b1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Tv_BVar b1))
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (f, uu___1)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_FVar.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_fv cb f in
          FStarC_Compiler_Util.bind_opt uu___2
            (fun f1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Tv_FVar f1))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (f, uu___1)::(us, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_UInst.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_fv cb f in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun f1 ->
               let uu___4 =
                 FStarC_TypeChecker_NBETerm.unembed
                   (FStarC_TypeChecker_NBETerm.e_list e_universe) cb us in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun us1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V2_Data.Tv_UInst (f1, us1))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (r, uu___1)::(l, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_App.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_term cb l in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun l1 ->
               let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_argv cb r in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun r1 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V2_Data.Tv_App (l1, r1))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (t1, uu___1)::(b, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Abs.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_binder cb b in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun b1 ->
               let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun t2 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V2_Data.Tv_Abs (b1, t2))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (t1, uu___1)::(b, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Arrow.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_binder cb b in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun b1 ->
               let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_comp cb t1 in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun c ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V2_Data.Tv_Arrow (b1, c))))
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (u, uu___1)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Type.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_universe cb u in
          FStarC_Compiler_Util.bind_opt uu___2
            (fun u1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Tv_Type u1))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (t1, uu___1)::(b, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Refine.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 = FStarC_TypeChecker_NBETerm.unembed e_binder cb b in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun b1 ->
               let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStarC_Compiler_Util.bind_opt uu___4
                 (fun t2 ->
                    FStar_Pervasives_Native.Some
                      (FStarC_Reflection_V2_Data.Tv_Refine (b1, t2))))
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (c, uu___1)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Const.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_vconst cb c in
          FStarC_Compiler_Util.bind_opt uu___2
            (fun c1 ->
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Tv_Const c1))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (l, uu___1)::(u, uu___2)::[]) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Uvar.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___3 =
            FStarC_TypeChecker_NBETerm.unembed
              FStarC_TypeChecker_NBETerm.e_int cb u in
          FStarC_Compiler_Util.bind_opt uu___3
            (fun u1 ->
               let ctx_u_s = unlazy_as_t FStarC_Syntax_Syntax.Lazy_uvar l in
               FStar_Pervasives_Native.Some
                 (FStarC_Reflection_V2_Data.Tv_Uvar (u1, ctx_u_s)))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___,
           (t2, uu___1)::(t1, uu___2)::(b, uu___3)::(attrs, uu___4)::
           (r, uu___5)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Let.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___6 =
            FStarC_TypeChecker_NBETerm.unembed
              FStarC_TypeChecker_NBETerm.e_bool cb r in
          FStarC_Compiler_Util.bind_opt uu___6
            (fun r1 ->
               let uu___7 =
                 FStarC_TypeChecker_NBETerm.unembed
                   (FStarC_TypeChecker_NBETerm.e_list e_term) cb attrs in
               FStarC_Compiler_Util.bind_opt uu___7
                 (fun attrs1 ->
                    let uu___8 =
                      FStarC_TypeChecker_NBETerm.unembed e_binder cb b in
                    FStarC_Compiler_Util.bind_opt uu___8
                      (fun b1 ->
                         let uu___9 =
                           FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
                         FStarC_Compiler_Util.bind_opt uu___9
                           (fun t11 ->
                              let uu___10 =
                                FStarC_TypeChecker_NBETerm.unembed e_term cb
                                  t2 in
                              FStarC_Compiler_Util.bind_opt uu___10
                                (fun t21 ->
                                   FStar_Pervasives_Native.Some
                                     (FStarC_Reflection_V2_Data.Tv_Let
                                        (r1, attrs1, b1, t11, t21)))))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___, (brs, uu___1)::(ret_opt, uu___2)::(t1, uu___3)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Match.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
          FStarC_Compiler_Util.bind_opt uu___4
            (fun t2 ->
               let uu___5 =
                 FStarC_TypeChecker_NBETerm.unembed
                   (FStarC_TypeChecker_NBETerm.e_list e_branch) cb brs in
               FStarC_Compiler_Util.bind_opt uu___5
                 (fun brs1 ->
                    let uu___6 =
                      FStarC_TypeChecker_NBETerm.unembed
                        e_match_returns_annotation cb ret_opt in
                    FStarC_Compiler_Util.bind_opt uu___6
                      (fun ret_opt1 ->
                         FStar_Pervasives_Native.Some
                           (FStarC_Reflection_V2_Data.Tv_Match
                              (t2, ret_opt1, brs1)))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___,
           (tacopt, uu___1)::(t1, uu___2)::(e, uu___3)::(use_eq, uu___4)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_AscT.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___5 = FStarC_TypeChecker_NBETerm.unembed e_term cb e in
          FStarC_Compiler_Util.bind_opt uu___5
            (fun e1 ->
               let uu___6 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
               FStarC_Compiler_Util.bind_opt uu___6
                 (fun t2 ->
                    let uu___7 =
                      FStarC_TypeChecker_NBETerm.unembed
                        (FStarC_TypeChecker_NBETerm.e_option e_term) cb
                        tacopt in
                    FStarC_Compiler_Util.bind_opt uu___7
                      (fun tacopt1 ->
                         let uu___8 =
                           FStarC_TypeChecker_NBETerm.unembed
                             FStarC_TypeChecker_NBETerm.e_bool cb use_eq in
                         FStarC_Compiler_Util.bind_opt uu___8
                           (fun use_eq1 ->
                              FStar_Pervasives_Native.Some
                                (FStarC_Reflection_V2_Data.Tv_AscribedT
                                   (e1, t2, tacopt1, use_eq1))))))
      | FStarC_TypeChecker_NBETerm.Construct
          (fv, uu___,
           (tacopt, uu___1)::(c, uu___2)::(e, uu___3)::(use_eq, uu___4)::[])
          when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_AscC.FStarC_Reflection_V2_Constants.lid
          ->
          let uu___5 = FStarC_TypeChecker_NBETerm.unembed e_term cb e in
          FStarC_Compiler_Util.bind_opt uu___5
            (fun e1 ->
               let uu___6 = FStarC_TypeChecker_NBETerm.unembed e_comp cb c in
               FStarC_Compiler_Util.bind_opt uu___6
                 (fun c1 ->
                    let uu___7 =
                      FStarC_TypeChecker_NBETerm.unembed
                        (FStarC_TypeChecker_NBETerm.e_option e_term) cb
                        tacopt in
                    FStarC_Compiler_Util.bind_opt uu___7
                      (fun tacopt1 ->
                         let uu___8 =
                           FStarC_TypeChecker_NBETerm.unembed
                             FStarC_TypeChecker_NBETerm.e_bool cb use_eq in
                         FStarC_Compiler_Util.bind_opt uu___8
                           (fun use_eq1 ->
                              FStar_Pervasives_Native.Some
                                (FStarC_Reflection_V2_Data.Tv_AscribedC
                                   (e1, c1, tacopt1, use_eq1))))))
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, []) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Unknown.FStarC_Reflection_V2_Constants.lid
          ->
          FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Tv_Unknown
      | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, []) when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Reflection_V2_Constants.ref_Tv_Unsupp.FStarC_Reflection_V2_Constants.lid
          -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Tv_Unsupp
      | uu___ ->
          ((let uu___2 =
              let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
              FStarC_Compiler_Util.format1 "Not an embedded term_view: %s"
                uu___3 in
            FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded
              () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2));
           FStar_Pervasives_Native.None) in
    mk_emb' embed_term_view unembed_term_view
      FStarC_Reflection_V2_Constants.fstar_refl_term_view_fv
let (e_term_view :
  FStarC_Reflection_V2_Data.term_view FStarC_TypeChecker_NBETerm.embedding) =
  e_term_view_aq (Prims.int_zero, [])
let (e_namedv_view :
  FStarC_Reflection_V2_Data.namedv_view FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_namedv_view cb namedvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_TypeChecker_NBETerm.embed FStarC_TypeChecker_NBETerm.e_int
            cb namedvv.FStarC_Reflection_V2_Data.uniq in
        FStarC_TypeChecker_NBETerm.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_TypeChecker_NBETerm.embed e_ppname cb
              namedvv.FStarC_Reflection_V2_Data.ppname in
          FStarC_TypeChecker_NBETerm.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_TypeChecker_NBETerm.embed e_sort cb
                namedvv.FStarC_Reflection_V2_Data.sort in
            FStarC_TypeChecker_NBETerm.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mkConstruct
      FStarC_Reflection_V2_Constants.ref_Mk_namedv_view.FStarC_Reflection_V2_Constants.fv
      [] uu___ in
  let unembed_namedv_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___, (sort, uu___1)::(ppname, uu___2)::(uniq, uu___3)::[])
        when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Mk_namedv_view.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___4 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb uniq in
        FStarC_Compiler_Util.bind_opt uu___4
          (fun uniq1 ->
             let uu___5 =
               FStarC_TypeChecker_NBETerm.unembed e_ppname cb ppname in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun ppname1 ->
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.unembed e_sort cb sort in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun sort1 ->
                       let r =
                         {
                           FStarC_Reflection_V2_Data.uniq = uniq1;
                           FStarC_Reflection_V2_Data.sort = sort1;
                           FStarC_Reflection_V2_Data.ppname = ppname1
                         } in
                       FStar_Pervasives_Native.Some r)))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded namedv_view: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_namedv_view unembed_namedv_view
    FStarC_Reflection_V2_Constants.fstar_refl_namedv_view_fv
let (e_bv_view :
  FStarC_Reflection_V2_Data.bv_view FStarC_TypeChecker_NBETerm.embedding) =
  let embed_bv_view cb bvv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_TypeChecker_NBETerm.embed FStarC_TypeChecker_NBETerm.e_int
            cb bvv.FStarC_Reflection_V2_Data.index in
        FStarC_TypeChecker_NBETerm.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_TypeChecker_NBETerm.embed e_ppname cb
              bvv.FStarC_Reflection_V2_Data.ppname1 in
          FStarC_TypeChecker_NBETerm.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_TypeChecker_NBETerm.embed e_sort cb
                bvv.FStarC_Reflection_V2_Data.sort1 in
            FStarC_TypeChecker_NBETerm.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mkConstruct
      FStarC_Reflection_V2_Constants.ref_Mk_bv_view.FStarC_Reflection_V2_Constants.fv
      [] uu___ in
  let unembed_bv_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___, (sort, uu___1)::(ppname, uu___2)::(idx, uu___3)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Mk_bv_view.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___4 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb idx in
        FStarC_Compiler_Util.bind_opt uu___4
          (fun idx1 ->
             let uu___5 =
               FStarC_TypeChecker_NBETerm.unembed e_ppname cb ppname in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun ppname1 ->
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.unembed e_sort cb sort in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun sort1 ->
                       let r =
                         {
                           FStarC_Reflection_V2_Data.index = idx1;
                           FStarC_Reflection_V2_Data.sort1 = sort1;
                           FStarC_Reflection_V2_Data.ppname1 = ppname1
                         } in
                       FStar_Pervasives_Native.Some r)))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded bv_view: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_bv_view unembed_bv_view
    FStarC_Reflection_V2_Constants.fstar_refl_bv_view_fv
let (e_attribute :
  FStarC_Syntax_Syntax.attribute FStarC_TypeChecker_NBETerm.embedding) =
  e_term
let (e_attributes :
  FStarC_Syntax_Syntax.attribute Prims.list
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_list e_attribute
let (e_binding :
  FStarC_Reflection_V2_Data.binding FStarC_TypeChecker_NBETerm.embedding) =
  let embed cb b =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_TypeChecker_NBETerm.embed FStarC_TypeChecker_NBETerm.e_int
            cb b.FStarC_Reflection_V2_Data.uniq1 in
        FStarC_TypeChecker_NBETerm.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_TypeChecker_NBETerm.embed e_term cb
              b.FStarC_Reflection_V2_Data.sort3 in
          FStarC_TypeChecker_NBETerm.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_TypeChecker_NBETerm.embed e_ppname cb
                b.FStarC_Reflection_V2_Data.ppname3 in
            FStarC_TypeChecker_NBETerm.as_arg uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mkConstruct
      FStarC_Reflection_V2_Constants.ref_Mk_binding.FStarC_Reflection_V2_Constants.fv
      [] uu___ in
  let unembed cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___, (ppname, uu___1)::(sort, uu___2)::(uniq, uu___3)::[])
        when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Mk_binding.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___4 =
          FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_int
            cb uniq in
        FStarC_Compiler_Util.bind_opt uu___4
          (fun uniq1 ->
             let uu___5 = FStarC_TypeChecker_NBETerm.unembed e_term cb sort in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun sort1 ->
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.unembed e_ppname cb ppname in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun ppname1 ->
                       let r =
                         {
                           FStarC_Reflection_V2_Data.uniq1 = uniq1;
                           FStarC_Reflection_V2_Data.sort3 = sort1;
                           FStarC_Reflection_V2_Data.ppname3 = ppname1
                         } in
                       FStar_Pervasives_Native.Some r))) in
  mk_emb' embed unembed FStarC_Reflection_V2_Constants.fstar_refl_binding_fv
let (e_binder_view :
  FStarC_Reflection_V2_Data.binder_view FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_binder_view cb bview =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_TypeChecker_NBETerm.embed e_term cb
            bview.FStarC_Reflection_V2_Data.sort2 in
        FStarC_TypeChecker_NBETerm.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_TypeChecker_NBETerm.embed e_aqualv cb
              bview.FStarC_Reflection_V2_Data.qual in
          FStarC_TypeChecker_NBETerm.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_TypeChecker_NBETerm.embed e_attributes cb
                bview.FStarC_Reflection_V2_Data.attrs in
            FStarC_TypeChecker_NBETerm.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                FStarC_TypeChecker_NBETerm.embed e_ppname cb
                  bview.FStarC_Reflection_V2_Data.ppname2 in
              FStarC_TypeChecker_NBETerm.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mkConstruct
      FStarC_Reflection_V2_Constants.ref_Mk_binder_view.FStarC_Reflection_V2_Constants.fv
      [] uu___ in
  let unembed_binder_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (ppname, uu___1)::(attrs, uu___2)::(q, uu___3)::(sort, uu___4)::[])
        when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Mk_binder_view.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___5 = FStarC_TypeChecker_NBETerm.unembed e_term cb sort in
        FStarC_Compiler_Util.bind_opt uu___5
          (fun sort1 ->
             let uu___6 = FStarC_TypeChecker_NBETerm.unembed e_aqualv cb q in
             FStarC_Compiler_Util.bind_opt uu___6
               (fun q1 ->
                  let uu___7 =
                    FStarC_TypeChecker_NBETerm.unembed e_attributes cb attrs in
                  FStarC_Compiler_Util.bind_opt uu___7
                    (fun attrs1 ->
                       let uu___8 =
                         FStarC_TypeChecker_NBETerm.unembed e_ppname cb
                           ppname in
                       FStarC_Compiler_Util.bind_opt uu___8
                         (fun ppname1 ->
                            let r =
                              {
                                FStarC_Reflection_V2_Data.sort2 = sort1;
                                FStarC_Reflection_V2_Data.qual = q1;
                                FStarC_Reflection_V2_Data.attrs = attrs1;
                                FStarC_Reflection_V2_Data.ppname2 = ppname1
                              } in
                            FStar_Pervasives_Native.Some r))))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded binder_view: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_binder_view unembed_binder_view
    FStarC_Reflection_V2_Constants.fstar_refl_binder_view_fv
let (e_comp_view :
  FStarC_Reflection_V2_Data.comp_view FStarC_TypeChecker_NBETerm.embedding) =
  let embed_comp_view cb cv =
    match cv with
    | FStarC_Reflection_V2_Data.C_Total t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_term cb t in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Total.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.C_GTotal t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_term cb t in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_GTotal.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_term cb pre in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_TypeChecker_NBETerm.embed e_term cb post in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_TypeChecker_NBETerm.embed e_term cb pats in
                FStarC_TypeChecker_NBETerm.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Lemma.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.C_Eff (us, eff, res, args, decrs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                (FStarC_TypeChecker_NBETerm.e_list e_universe) cb us in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_TypeChecker_NBETerm.embed
                  FStarC_TypeChecker_NBETerm.e_string_list cb eff in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_TypeChecker_NBETerm.embed e_term cb res in
                FStarC_TypeChecker_NBETerm.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_TypeChecker_NBETerm.embed
                      (FStarC_TypeChecker_NBETerm.e_list e_argv) cb args in
                  FStarC_TypeChecker_NBETerm.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      FStarC_TypeChecker_NBETerm.embed
                        (FStarC_TypeChecker_NBETerm.e_list e_term) cb decrs in
                    FStarC_TypeChecker_NBETerm.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_C_Eff.FStarC_Reflection_V2_Constants.fv
          [] uu___ in
  let unembed_comp_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (t1, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Total.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun t2 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.C_Total t2))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, (t1, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_GTotal.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___2 = FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun t2 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.C_GTotal t2))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___, (post, uu___1)::(pre, uu___2)::(pats, uu___3)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Lemma.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_term cb pre in
        FStarC_Compiler_Util.bind_opt uu___4
          (fun pre1 ->
             let uu___5 = FStarC_TypeChecker_NBETerm.unembed e_term cb post in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun post1 ->
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.unembed e_term cb pats in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun pats1 ->
                       FStar_Pervasives_Native.Some
                         (FStarC_Reflection_V2_Data.C_Lemma
                            (pre1, post1, pats1)))))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (decrs, uu___1)::(args, uu___2)::(res, uu___3)::(eff, uu___4)::
         (us, uu___5)::[])
        when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_C_Eff.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___6 =
          FStarC_TypeChecker_NBETerm.unembed
            (FStarC_TypeChecker_NBETerm.e_list e_universe) cb us in
        FStarC_Compiler_Util.bind_opt uu___6
          (fun us1 ->
             let uu___7 =
               FStarC_TypeChecker_NBETerm.unembed
                 FStarC_TypeChecker_NBETerm.e_string_list cb eff in
             FStarC_Compiler_Util.bind_opt uu___7
               (fun eff1 ->
                  let uu___8 =
                    FStarC_TypeChecker_NBETerm.unembed e_term cb res in
                  FStarC_Compiler_Util.bind_opt uu___8
                    (fun res1 ->
                       let uu___9 =
                         FStarC_TypeChecker_NBETerm.unembed
                           (FStarC_TypeChecker_NBETerm.e_list e_argv) cb args in
                       FStarC_Compiler_Util.bind_opt uu___9
                         (fun args1 ->
                            let uu___10 =
                              FStarC_TypeChecker_NBETerm.unembed
                                (FStarC_TypeChecker_NBETerm.e_list e_term) cb
                                decrs in
                            FStarC_Compiler_Util.bind_opt uu___10
                              (fun decrs1 ->
                                 FStar_Pervasives_Native.Some
                                   (FStarC_Reflection_V2_Data.C_Eff
                                      (us1, eff1, res1, args1, decrs1)))))))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded comp_view: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_comp_view unembed_comp_view
    FStarC_Reflection_V2_Constants.fstar_refl_comp_view_fv
let (e_sigelt :
  FStarC_Syntax_Syntax.sigelt FStarC_TypeChecker_NBETerm.embedding) =
  let embed_sigelt cb se =
    mk_lazy cb se FStarC_Reflection_V2_Constants.fstar_refl_sigelt
      FStarC_Syntax_Syntax.Lazy_sigelt in
  let unembed_sigelt cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = b;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_sigelt;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn b in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded sigelt: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt unembed_sigelt
    FStarC_Reflection_V2_Constants.fstar_refl_sigelt_fv
let (e_string_list :
  Prims.string Prims.list FStarC_TypeChecker_NBETerm.embedding) =
  FStarC_TypeChecker_NBETerm.e_list FStarC_TypeChecker_NBETerm.e_string
let (e_ctor :
  (Prims.string Prims.list * FStarC_Syntax_Syntax.term)
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_tuple2 e_string_list e_term
let (e_lb_view :
  FStarC_Reflection_V2_Data.lb_view FStarC_TypeChecker_NBETerm.embedding) =
  let embed_lb_view cb lbv =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_TypeChecker_NBETerm.embed e_fv cb
            lbv.FStarC_Reflection_V2_Data.lb_fv in
        FStarC_TypeChecker_NBETerm.as_arg uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_TypeChecker_NBETerm.embed e_univ_names cb
              lbv.FStarC_Reflection_V2_Data.lb_us in
          FStarC_TypeChecker_NBETerm.as_arg uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_TypeChecker_NBETerm.embed e_term cb
                lbv.FStarC_Reflection_V2_Data.lb_typ in
            FStarC_TypeChecker_NBETerm.as_arg uu___6 in
          let uu___6 =
            let uu___7 =
              let uu___8 =
                FStarC_TypeChecker_NBETerm.embed e_term cb
                  lbv.FStarC_Reflection_V2_Data.lb_def in
              FStarC_TypeChecker_NBETerm.as_arg uu___8 in
            [uu___7] in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mkConstruct
      FStarC_Reflection_V2_Constants.ref_Mk_lb.FStarC_Reflection_V2_Constants.fv
      [] uu___ in
  let unembed_lb_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (fv', uu___1)::(us, uu___2)::(typ, uu___3)::(def, uu___4)::[])
        when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Mk_lb.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___5 = FStarC_TypeChecker_NBETerm.unembed e_fv cb fv' in
        FStarC_Compiler_Util.bind_opt uu___5
          (fun fv'1 ->
             let uu___6 =
               FStarC_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStarC_Compiler_Util.bind_opt uu___6
               (fun us1 ->
                  let uu___7 =
                    FStarC_TypeChecker_NBETerm.unembed e_term cb typ in
                  FStarC_Compiler_Util.bind_opt uu___7
                    (fun typ1 ->
                       let uu___8 =
                         FStarC_TypeChecker_NBETerm.unembed e_term cb def in
                       FStarC_Compiler_Util.bind_opt uu___8
                         (fun def1 ->
                            FStar_Pervasives_Native.Some
                              {
                                FStarC_Reflection_V2_Data.lb_fv = fv'1;
                                FStarC_Reflection_V2_Data.lb_us = us1;
                                FStarC_Reflection_V2_Data.lb_typ = typ1;
                                FStarC_Reflection_V2_Data.lb_def = def1
                              }))))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded lb_view: %s" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_lb_view unembed_lb_view
    FStarC_Reflection_V2_Constants.fstar_refl_lb_view_fv
let (e_lid : FStarC_Ident.lid FStarC_TypeChecker_NBETerm.embedding) =
  let embed rng lid =
    let uu___ = FStarC_Ident.path_of_lid lid in
    FStarC_TypeChecker_NBETerm.embed e_string_list rng uu___ in
  let unembed cb t =
    let uu___ = FStarC_TypeChecker_NBETerm.unembed e_string_list cb t in
    FStarC_Compiler_Util.map_opt uu___
      (fun p ->
         FStarC_Ident.lid_of_path p FStarC_Compiler_Range_Type.dummyRange) in
  FStarC_TypeChecker_NBETerm.mk_emb embed unembed
    (fun uu___ ->
       mkConstruct FStarC_Reflection_V2_Constants.fstar_refl_aqualv_fv [] [])
    (fun uu___ ->
       fv_as_emb_typ FStarC_Reflection_V2_Constants.fstar_refl_aqualv_fv)
let (e_letbinding :
  FStarC_Syntax_Syntax.letbinding FStarC_TypeChecker_NBETerm.embedding) =
  let embed_letbinding cb lb =
    mk_lazy cb lb FStarC_Reflection_V2_Constants.fstar_refl_letbinding
      FStarC_Syntax_Syntax.Lazy_letbinding in
  let unembed_letbinding cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = lb;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_letbinding;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn lb in
        FStar_Pervasives_Native.Some uu___3
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded letbinding: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_letbinding unembed_letbinding
    FStarC_Reflection_V2_Constants.fstar_refl_letbinding_fv
let (e_sigelt_view :
  FStarC_Reflection_V2_Data.sigelt_view FStarC_TypeChecker_NBETerm.embedding)
  =
  let embed_sigelt_view cb sev =
    match sev with
    | FStarC_Reflection_V2_Data.Sg_Let (r, lbs) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                FStarC_TypeChecker_NBETerm.e_bool cb r in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_TypeChecker_NBETerm.embed
                  (FStarC_TypeChecker_NBETerm.e_list e_letbinding) cb lbs in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Sg_Let.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Sg_Inductive (nm, univs, bs, t, dcs) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_TypeChecker_NBETerm.embed e_univ_names cb univs in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_TypeChecker_NBETerm.embed e_binders cb bs in
                FStarC_TypeChecker_NBETerm.as_arg uu___6 in
              let uu___6 =
                let uu___7 =
                  let uu___8 = FStarC_TypeChecker_NBETerm.embed e_term cb t in
                  FStarC_TypeChecker_NBETerm.as_arg uu___8 in
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      FStarC_TypeChecker_NBETerm.embed
                        (FStarC_TypeChecker_NBETerm.e_list e_ctor) cb dcs in
                    FStarC_TypeChecker_NBETerm.as_arg uu___10 in
                  [uu___9] in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Sg_Inductive.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Sg_Val (nm, univs, t) ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_string_list cb nm in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_TypeChecker_NBETerm.embed e_univ_names cb univs in
              FStarC_TypeChecker_NBETerm.as_arg uu___4 in
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_TypeChecker_NBETerm.embed e_term cb t in
                FStarC_TypeChecker_NBETerm.as_arg uu___6 in
              [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Sg_Val.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Unk ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_Unk.FStarC_Reflection_V2_Constants.fv
          [] [] in
  let unembed_sigelt_view cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___,
         (dcs, uu___1)::(t1, uu___2)::(bs, uu___3)::(us, uu___4)::(nm,
                                                                   uu___5)::[])
        when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Sg_Inductive.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___6 = FStarC_TypeChecker_NBETerm.unembed e_string_list cb nm in
        FStarC_Compiler_Util.bind_opt uu___6
          (fun nm1 ->
             let uu___7 =
               FStarC_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStarC_Compiler_Util.bind_opt uu___7
               (fun us1 ->
                  let uu___8 =
                    FStarC_TypeChecker_NBETerm.unembed e_binders cb bs in
                  FStarC_Compiler_Util.bind_opt uu___8
                    (fun bs1 ->
                       let uu___9 =
                         FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
                       FStarC_Compiler_Util.bind_opt uu___9
                         (fun t2 ->
                            let uu___10 =
                              FStarC_TypeChecker_NBETerm.unembed
                                (FStarC_TypeChecker_NBETerm.e_list e_ctor) cb
                                dcs in
                            FStarC_Compiler_Util.bind_opt uu___10
                              (fun dcs1 ->
                                 FStar_Pervasives_Native.Some
                                   (FStarC_Reflection_V2_Data.Sg_Inductive
                                      (nm1, us1, bs1, t2, dcs1)))))))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___, (lbs, uu___1)::(r, uu___2)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Sg_Let.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___3 =
          FStarC_TypeChecker_NBETerm.unembed
            FStarC_TypeChecker_NBETerm.e_bool cb r in
        FStarC_Compiler_Util.bind_opt uu___3
          (fun r1 ->
             let uu___4 =
               FStarC_TypeChecker_NBETerm.unembed
                 (FStarC_TypeChecker_NBETerm.e_list e_letbinding) cb lbs in
             FStarC_Compiler_Util.bind_opt uu___4
               (fun lbs1 ->
                  FStar_Pervasives_Native.Some
                    (FStarC_Reflection_V2_Data.Sg_Let (r1, lbs1))))
    | FStarC_TypeChecker_NBETerm.Construct
        (fv, uu___, (t1, uu___1)::(us, uu___2)::(nm, uu___3)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Sg_Val.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___4 = FStarC_TypeChecker_NBETerm.unembed e_string_list cb nm in
        FStarC_Compiler_Util.bind_opt uu___4
          (fun nm1 ->
             let uu___5 =
               FStarC_TypeChecker_NBETerm.unembed e_univ_names cb us in
             FStarC_Compiler_Util.bind_opt uu___5
               (fun us1 ->
                  let uu___6 =
                    FStarC_TypeChecker_NBETerm.unembed e_term cb t1 in
                  FStarC_Compiler_Util.bind_opt uu___6
                    (fun t2 ->
                       FStar_Pervasives_Native.Some
                         (FStarC_Reflection_V2_Data.Sg_Val (nm1, us1, t2)))))
    | FStarC_TypeChecker_NBETerm.Construct (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_Unk.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Unk
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded sigelt_view: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb' embed_sigelt_view unembed_sigelt_view
    FStarC_Reflection_V2_Constants.fstar_refl_sigelt_view_fv
let (e_name :
  FStarC_Reflection_V2_Data.name FStarC_TypeChecker_NBETerm.embedding) =
  FStarC_TypeChecker_NBETerm.e_list FStarC_TypeChecker_NBETerm.e_string
let (e_qualifier :
  FStarC_Reflection_V2_Data.qualifier FStarC_TypeChecker_NBETerm.embedding) =
  let embed cb q =
    match q with
    | FStarC_Reflection_V2_Data.Assumption ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Assumption.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.New ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_New.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Private ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Private.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Unfold_for_unification_and_vcgen ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Visible_default ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Visible_default.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Irreducible ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Irreducible.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Inline_for_extraction ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Inline_for_extraction.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.NoExtract ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_NoExtract.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Noeq ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Noeq.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Unopteq ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Unopteq.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.TotalEffect ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_TotalEffect.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Logic ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Logic.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Reifiable ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Reifiable.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.ExceptionConstructor ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_ExceptionConstructor.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.HasMaskedEffect ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_HasMaskedEffect.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Effect ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Effect.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.OnlyName ->
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_OnlyName.FStarC_Reflection_V2_Constants.fv
          [] []
    | FStarC_Reflection_V2_Data.Reflectable l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_name cb l in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Reflectable.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Discriminator l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_name cb l in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Discriminator.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Action l ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed e_name cb l in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Action.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.Projector li ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                (FStarC_TypeChecker_NBETerm.e_tuple2 e_name e_ident) cb li in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_Projector.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.RecordType ids12 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                (FStarC_TypeChecker_NBETerm.e_tuple2
                   (FStarC_TypeChecker_NBETerm.e_list e_ident)
                   (FStarC_TypeChecker_NBETerm.e_list e_ident)) cb ids12 in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_RecordType.FStarC_Reflection_V2_Constants.fv
          [] uu___
    | FStarC_Reflection_V2_Data.RecordConstructor ids12 ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_TypeChecker_NBETerm.embed
                (FStarC_TypeChecker_NBETerm.e_tuple2
                   (FStarC_TypeChecker_NBETerm.e_list e_ident)
                   (FStarC_TypeChecker_NBETerm.e_list e_ident)) cb ids12 in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          [uu___1] in
        mkConstruct
          FStarC_Reflection_V2_Constants.ref_qual_RecordConstructor.FStarC_Reflection_V2_Constants.fv
          [] uu___ in
  let unembed cb t =
    match t.FStarC_TypeChecker_NBETerm.nbe_t with
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Assumption.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Assumption
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_New.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.New
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Private.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Private
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Unfold_for_unification_and_vcgen.FStarC_Reflection_V2_Constants.lid
        ->
        FStar_Pervasives_Native.Some
          FStarC_Reflection_V2_Data.Unfold_for_unification_and_vcgen
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Visible_default.FStarC_Reflection_V2_Constants.lid
        ->
        FStar_Pervasives_Native.Some
          FStarC_Reflection_V2_Data.Visible_default
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Irreducible.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Irreducible
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Inline_for_extraction.FStarC_Reflection_V2_Constants.lid
        ->
        FStar_Pervasives_Native.Some
          FStarC_Reflection_V2_Data.Inline_for_extraction
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_NoExtract.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.NoExtract
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Noeq.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Noeq
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Unopteq.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Unopteq
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_TotalEffect.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.TotalEffect
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Logic.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Logic
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Reifiable.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Reifiable
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_ExceptionConstructor.FStarC_Reflection_V2_Constants.lid
        ->
        FStar_Pervasives_Native.Some
          FStarC_Reflection_V2_Data.ExceptionConstructor
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_HasMaskedEffect.FStarC_Reflection_V2_Constants.lid
        ->
        FStar_Pervasives_Native.Some
          FStarC_Reflection_V2_Data.HasMaskedEffect
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Effect.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.Effect
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_OnlyName.FStarC_Reflection_V2_Constants.lid
        -> FStar_Pervasives_Native.Some FStarC_Reflection_V2_Data.OnlyName
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (l, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Reflectable.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 = FStarC_TypeChecker_NBETerm.unembed e_name cb l in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Reflectable l1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (l, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Discriminator.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 = FStarC_TypeChecker_NBETerm.unembed e_name cb l in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Discriminator l1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (l, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Action.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 = FStarC_TypeChecker_NBETerm.unembed e_name cb l in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun l1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Action l1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (li, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_Projector.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed
            (FStarC_TypeChecker_NBETerm.e_tuple2 e_name e_ident) cb li in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun li1 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.Projector li1))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (ids12, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_RecordType.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed
            (FStarC_TypeChecker_NBETerm.e_tuple2
               (FStarC_TypeChecker_NBETerm.e_list e_ident)
               (FStarC_TypeChecker_NBETerm.e_list e_ident)) cb ids12 in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun ids121 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.RecordType ids121))
    | FStarC_TypeChecker_NBETerm.Construct (fv, [], (ids12, uu___)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Reflection_V2_Constants.ref_qual_RecordConstructor.FStarC_Reflection_V2_Constants.lid
        ->
        let uu___1 =
          FStarC_TypeChecker_NBETerm.unembed
            (FStarC_TypeChecker_NBETerm.e_tuple2
               (FStarC_TypeChecker_NBETerm.e_list e_ident)
               (FStarC_TypeChecker_NBETerm.e_list e_ident)) cb ids12 in
        FStarC_Compiler_Util.bind_opt uu___1
          (fun ids121 ->
             FStar_Pervasives_Native.Some
               (FStarC_Reflection_V2_Data.RecordConstructor ids121))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = FStarC_TypeChecker_NBETerm.t_to_string t in
            FStarC_Compiler_Util.format1 "Not an embedded qualifier: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  FStarC_TypeChecker_NBETerm.mk_emb embed unembed
    (fun uu___ ->
       mkConstruct FStarC_Reflection_V2_Constants.fstar_refl_qualifier_fv []
         [])
    (fun uu___ ->
       fv_as_emb_typ FStarC_Reflection_V2_Constants.fstar_refl_qualifier_fv)
let (e_qualifiers :
  FStarC_Reflection_V2_Data.qualifier Prims.list
    FStarC_TypeChecker_NBETerm.embedding)
  = FStarC_TypeChecker_NBETerm.e_list e_qualifier
let (e_vconfig :
  FStarC_Compiler_Order.order FStarC_TypeChecker_NBETerm.embedding) =
  let emb cb o = failwith "emb vconfig NBE" in
  let unemb cb t = failwith "unemb vconfig NBE" in
  let uu___ =
    FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.vconfig_lid
      FStar_Pervasives_Native.None in
  mk_emb' emb unemb uu___