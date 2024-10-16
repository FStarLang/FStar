open Prims
let (dbg_PartialApp : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "PartialApp"
exception Inner_let_rec of (Prims.string * FStarC_Compiler_Range_Type.range)
  Prims.list 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Inner_let_rec uu___ -> true | uu___ -> false
let (__proj__Inner_let_rec__item__uu___ :
  Prims.exn -> (Prims.string * FStarC_Compiler_Range_Type.range) Prims.list)
  = fun projectee -> match projectee with | Inner_let_rec uu___ -> uu___
let add_fuel : 'uuuuu . 'uuuuu -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun x ->
    fun tl ->
      let uu___ = FStarC_Options.unthrottle_inductives () in
      if uu___ then tl else x :: tl
let withenv :
  'uuuuu 'uuuuu1 'uuuuu2 .
    'uuuuu -> ('uuuuu1 * 'uuuuu2) -> ('uuuuu1 * 'uuuuu2 * 'uuuuu)
  = fun c -> fun uu___ -> match uu___ with | (a, b) -> (a, b, c)
let vargs :
  'uuuuu 'uuuuu1 'uuuuu2 .
    (('uuuuu, 'uuuuu1) FStar_Pervasives.either * 'uuuuu2) Prims.list ->
      (('uuuuu, 'uuuuu1) FStar_Pervasives.either * 'uuuuu2) Prims.list
  =
  fun args ->
    FStarC_Compiler_List.filter
      (fun uu___ ->
         match uu___ with
         | (FStar_Pervasives.Inl uu___1, uu___2) -> false
         | uu___1 -> true) args
let (escape : Prims.string -> Prims.string) =
  fun s -> FStarC_Compiler_Util.replace_char s 39 95
let (mk_term_projector_name :
  FStarC_Ident.lident -> FStarC_Syntax_Syntax.bv -> Prims.string) =
  fun lid ->
    fun a ->
      let uu___ =
        let uu___1 = FStarC_Ident.string_of_lid lid in
        let uu___2 = FStarC_Ident.string_of_id a.FStarC_Syntax_Syntax.ppname in
        FStarC_Compiler_Util.format2 "%s_%s" uu___1 uu___2 in
      escape uu___
let (primitive_projector_by_pos :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env ->
    fun lid ->
      fun i ->
        let fail uu___ =
          let uu___1 =
            let uu___2 = FStarC_Ident.string_of_lid lid in
            FStarC_Compiler_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) uu___2 in
          failwith uu___1 in
        let uu___ = FStarC_TypeChecker_Env.lookup_datacon env lid in
        match uu___ with
        | (uu___1, t) ->
            let uu___2 =
              let uu___3 = FStarC_Syntax_Subst.compress t in
              uu___3.FStarC_Syntax_Syntax.n in
            (match uu___2 with
             | FStarC_Syntax_Syntax.Tm_arrow
                 { FStarC_Syntax_Syntax.bs1 = bs;
                   FStarC_Syntax_Syntax.comp = c;_}
                 ->
                 let uu___3 = FStarC_Syntax_Subst.open_comp bs c in
                 (match uu___3 with
                  | (binders, uu___4) ->
                      if
                        (i < Prims.int_zero) ||
                          (i >= (FStarC_Compiler_List.length binders))
                      then fail ()
                      else
                        (let b = FStarC_Compiler_List.nth binders i in
                         mk_term_projector_name lid
                           b.FStarC_Syntax_Syntax.binder_bv))
             | uu___3 -> fail ())
let (mk_term_projector_name_by_pos :
  FStarC_Ident.lident -> Prims.int -> Prims.string) =
  fun lid ->
    fun i ->
      let uu___ =
        let uu___1 = FStarC_Ident.string_of_lid lid in
        FStarC_Compiler_Util.format2 "%s_%s" uu___1 (Prims.string_of_int i) in
      escape uu___
let (mk_term_projector :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.bv -> FStarC_SMTEncoding_Term.term)
  =
  fun lid ->
    fun a ->
      let uu___ =
        let uu___1 =
          let uu___2 = mk_term_projector_name lid a in
          (uu___2,
            (FStarC_SMTEncoding_Term.Arrow
               (FStarC_SMTEncoding_Term.Term_sort,
                 FStarC_SMTEncoding_Term.Term_sort))) in
        FStarC_SMTEncoding_Term.mk_fv uu___1 in
      FStarC_SMTEncoding_Util.mkFreeV uu___
let (mk_term_projector_by_pos :
  FStarC_Ident.lident -> Prims.int -> FStarC_SMTEncoding_Term.term) =
  fun lid ->
    fun i ->
      let uu___ =
        let uu___1 =
          let uu___2 = mk_term_projector_name_by_pos lid i in
          (uu___2,
            (FStarC_SMTEncoding_Term.Arrow
               (FStarC_SMTEncoding_Term.Term_sort,
                 FStarC_SMTEncoding_Term.Term_sort))) in
        FStarC_SMTEncoding_Term.mk_fv uu___1 in
      FStarC_SMTEncoding_Util.mkFreeV uu___
let mk_data_tester :
  'uuuuu .
    'uuuuu ->
      FStarC_Ident.lident ->
        FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term
  =
  fun env ->
    fun l ->
      fun x ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid l in escape uu___1 in
        FStarC_SMTEncoding_Term.mk_tester uu___ x
type varops_t =
  {
  push: unit -> unit ;
  pop: unit -> unit ;
  snapshot: unit -> (Prims.int * unit) ;
  rollback: Prims.int FStar_Pervasives_Native.option -> unit ;
  new_var: FStarC_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStarC_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string -> Prims.string ;
  reset_fresh: unit -> unit ;
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let (__proj__Mkvarops_t__item__push : varops_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> push
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> pop
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int * unit)) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> snapshot
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> rollback
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStarC_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> new_var
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStarC_Ident.lident -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> new_fvar
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> fresh
let (__proj__Mkvarops_t__item__reset_fresh : varops_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> reset_fresh
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> next_id
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> mk_unique
let (varops : varops_t) =
  let initial_ctr = (Prims.of_int (100)) in
  let ctr = FStarC_Compiler_Util.mk_ref initial_ctr in
  let new_scope uu___ = FStarC_Compiler_Util.smap_create (Prims.of_int (100)) in
  let scopes =
    let uu___ = let uu___1 = new_scope () in [uu___1] in
    FStarC_Compiler_Util.mk_ref uu___ in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu___ =
        let uu___1 = FStarC_Compiler_Effect.op_Bang scopes in
        FStarC_Compiler_Util.find_map uu___1
          (fun names -> FStarC_Compiler_Util.smap_try_find names y1) in
      match uu___ with
      | FStar_Pervasives_Native.None -> y1
      | FStar_Pervasives_Native.Some uu___1 ->
          (FStarC_Compiler_Util.incr ctr;
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Compiler_Effect.op_Bang ctr in
                Prims.string_of_int uu___5 in
              Prims.strcat "__" uu___4 in
            Prims.strcat y1 uu___3)) in
    let top_scope =
      let uu___ = FStarC_Compiler_Effect.op_Bang scopes in
      FStarC_Compiler_List.hd uu___ in
    FStarC_Compiler_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_id pp in
      Prims.strcat uu___1 (Prims.strcat "__" (Prims.string_of_int rn)) in
    mk_unique uu___ in
  let new_fvar lid =
    let uu___ = FStarC_Ident.string_of_lid lid in mk_unique uu___ in
  let next_id uu___ =
    FStarC_Compiler_Util.incr ctr; FStarC_Compiler_Effect.op_Bang ctr in
  let fresh mname pfx =
    let uu___ = let uu___1 = next_id () in Prims.string_of_int uu___1 in
    FStarC_Compiler_Util.format3 "%s_%s_%s" pfx mname uu___ in
  let reset_fresh uu___ =
    FStarC_Compiler_Effect.op_Colon_Equals ctr initial_ctr in
  let push uu___ =
    let uu___1 =
      let uu___2 = new_scope () in
      let uu___3 = FStarC_Compiler_Effect.op_Bang scopes in uu___2 :: uu___3 in
    FStarC_Compiler_Effect.op_Colon_Equals scopes uu___1 in
  let pop uu___ =
    let uu___1 =
      let uu___2 = FStarC_Compiler_Effect.op_Bang scopes in
      FStarC_Compiler_List.tl uu___2 in
    FStarC_Compiler_Effect.op_Colon_Equals scopes uu___1 in
  let snapshot uu___ = FStarC_Common.snapshot push scopes () in
  let rollback depth = FStarC_Common.rollback pop scopes depth in
  {
    push;
    pop;
    snapshot;
    rollback;
    new_var;
    new_fvar;
    fresh;
    reset_fresh;
    next_id;
    mk_unique
  }
type fvar_binding =
  {
  fvar_lid: FStarC_Ident.lident ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term)
      FStar_Pervasives_Native.option
    ;
  fvb_thunked: Prims.bool }
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> fvar_lid
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_arity
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_id
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_token
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding ->
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_fuel_partial_app
let (__proj__Mkfvar_binding__item__fvb_thunked : fvar_binding -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> fvb_thunked
let (fvb_to_string : fvar_binding -> Prims.string) =
  fun fvb ->
    let term_opt_to_string uu___ =
      match uu___ with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some s ->
          FStarC_SMTEncoding_Term.print_smt_term s in
    let term_pair_opt_to_string uu___ =
      match uu___ with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some (s0, s1) ->
          let uu___1 = FStarC_SMTEncoding_Term.print_smt_term s0 in
          let uu___2 = FStarC_SMTEncoding_Term.print_smt_term s1 in
          FStarC_Compiler_Util.format2 "(%s, %s)" uu___1 uu___2 in
    let uu___ = FStarC_Ident.string_of_lid fvb.fvar_lid in
    let uu___1 = term_opt_to_string fvb.smt_token in
    let uu___2 = term_pair_opt_to_string fvb.smt_fuel_partial_app in
    let uu___3 = FStarC_Compiler_Util.string_of_bool fvb.fvb_thunked in
    FStarC_Compiler_Util.format6
      "{ lid = %s;\n  smt_arity = %s;\n  smt_id = %s;\n  smt_token = %s;\n  smt_fuel_partial_app = %s;\n  fvb_thunked = %s }"
      uu___ (Prims.string_of_int fvb.smt_arity) fvb.smt_id uu___1 uu___2
      uu___3
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb ->
    if
      ((FStarC_Compiler_Option.isSome fvb.smt_token) ||
         (FStarC_Compiler_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu___1 =
         let uu___2 = FStarC_Ident.string_of_lid fvb.fvar_lid in
         FStarC_Compiler_Util.format1 "Unexpected thunked SMT symbol: %s"
           uu___2 in
       failwith uu___1)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> Prims.int_zero)
      then
        (let uu___2 =
           let uu___3 = FStarC_Ident.string_of_lid fvb.fvar_lid in
           FStarC_Compiler_Util.format1
             "Unexpected arity of thunked SMT symbol: %s" uu___3 in
         failwith uu___2)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         { FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.FreeV uu___1;
           FStarC_SMTEncoding_Term.freevars = uu___2;
           FStarC_SMTEncoding_Term.rng = uu___3;_}
         ->
         let uu___4 =
           let uu___5 = fvb_to_string fvb in
           FStarC_Compiler_Util.format1 "bad fvb\n%s" uu___5 in
         failwith uu___4
     | uu___1 -> ())
let binder_of_eithervar :
  'uuuuu 'uuuuu1 .
    'uuuuu -> ('uuuuu * 'uuuuu1 FStar_Pervasives_Native.option)
  = fun v -> (v, FStar_Pervasives_Native.None)
type env_t =
  {
  bvar_bindings:
    (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term)
      FStarC_Compiler_Util.pimap FStarC_Compiler_Util.psmap
    ;
  fvar_bindings:
    (fvar_binding FStarC_Compiler_Util.psmap * fvar_binding Prims.list) ;
  depth: Prims.int ;
  tcenv: FStarC_TypeChecker_Env.env ;
  warn: Prims.bool ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string ;
  encoding_quantifier: Prims.bool ;
  global_cache: FStarC_SMTEncoding_Term.decls_elt FStarC_Compiler_Util.smap }
let (__proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term)
      FStarC_Compiler_Util.pimap FStarC_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> bvar_bindings
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t ->
    (fvar_binding FStarC_Compiler_Util.psmap * fvar_binding Prims.list))
  =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> fvar_bindings
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> depth
let (__proj__Mkenv_t__item__tcenv : env_t -> FStarC_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> tcenv
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> warn
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> nolabels
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> use_zfuel_name
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> encode_non_total_function_typ
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> current_module_name
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> encoding_quantifier
let (__proj__Mkenv_t__item__global_cache :
  env_t -> FStarC_SMTEncoding_Term.decls_elt FStarC_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> global_cache
let (print_env : env_t -> Prims.string) =
  fun e ->
    let bvars =
      FStarC_Compiler_Util.psmap_fold e.bvar_bindings
        (fun _k ->
           fun pi ->
             fun acc ->
               FStarC_Compiler_Util.pimap_fold pi
                 (fun _i ->
                    fun uu___ ->
                      fun acc1 ->
                        match uu___ with
                        | (x, _term) ->
                            let uu___1 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_bv x in
                            uu___1 :: acc1) acc) [] in
    let allvars =
      FStarC_Compiler_Util.psmap_fold
        (FStar_Pervasives_Native.fst e.fvar_bindings)
        (fun _k -> fun fvb -> fun acc -> (fvb.fvar_lid) :: acc) [] in
    let last_fvar =
      match FStarC_Compiler_List.rev allvars with
      | [] -> ""
      | l::uu___ ->
          let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident l in
          Prims.strcat "...," uu___1 in
    FStarC_Compiler_String.concat ", " (last_fvar :: bvars)
let (lookup_bvar_binding :
  env_t ->
    FStarC_Syntax_Syntax.bv ->
      (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun bv ->
      let uu___ =
        let uu___1 = FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname in
        FStarC_Compiler_Util.psmap_try_find env.bvar_bindings uu___1 in
      match uu___ with
      | FStar_Pervasives_Native.Some bvs ->
          FStarC_Compiler_Util.pimap_try_find bvs
            bv.FStarC_Syntax_Syntax.index
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lookup_fvar_binding :
  env_t -> FStarC_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu___ = FStarC_Ident.string_of_lid lid in
      FStarC_Compiler_Util.psmap_try_find
        (FStar_Pervasives_Native.fst env.fvar_bindings) uu___
let add_bvar_binding :
  'uuuuu .
    (FStarC_Syntax_Syntax.bv * 'uuuuu) ->
      (FStarC_Syntax_Syntax.bv * 'uuuuu) FStarC_Compiler_Util.pimap
        FStarC_Compiler_Util.psmap ->
        (FStarC_Syntax_Syntax.bv * 'uuuuu) FStarC_Compiler_Util.pimap
          FStarC_Compiler_Util.psmap
  =
  fun bvb ->
    fun bvbs ->
      let uu___ =
        FStarC_Ident.string_of_id
          (FStar_Pervasives_Native.fst bvb).FStarC_Syntax_Syntax.ppname in
      FStarC_Compiler_Util.psmap_modify bvbs uu___
        (fun pimap_opt ->
           let uu___1 =
             let uu___2 = FStarC_Compiler_Util.pimap_empty () in
             FStarC_Compiler_Util.dflt uu___2 pimap_opt in
           FStarC_Compiler_Util.pimap_add uu___1
             (FStar_Pervasives_Native.fst bvb).FStarC_Syntax_Syntax.index bvb)
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStarC_Compiler_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStarC_Compiler_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb ->
    fun uu___ ->
      match uu___ with
      | (fvb_map, fvb_list) ->
          let uu___1 =
            let uu___2 = FStarC_Ident.string_of_lid fvb.fvar_lid in
            FStarC_Compiler_Util.psmap_add fvb_map uu___2 fvb in
          (uu___1, (fvb :: fvb_list))
let (fresh_fvar :
  Prims.string ->
    Prims.string ->
      FStarC_SMTEncoding_Term.sort ->
        (Prims.string * FStarC_SMTEncoding_Term.term))
  =
  fun mname ->
    fun x ->
      fun s ->
        let xsym = varops.fresh mname x in
        let uu___ =
          let uu___1 = FStarC_SMTEncoding_Term.mk_fv (xsym, s) in
          FStarC_SMTEncoding_Util.mkFreeV uu___1 in
        (xsym, uu___)
let (gen_term_var :
  env_t ->
    FStarC_Syntax_Syntax.bv ->
      (Prims.string * FStarC_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        let uu___ =
          FStarC_SMTEncoding_Term.mk_fv
            (ysym, FStarC_SMTEncoding_Term.Term_sort) in
        FStarC_SMTEncoding_Util.mkFreeV uu___ in
      let uu___ =
        let uu___1 = add_bvar_binding (x, y) env.bvar_bindings in
        let uu___2 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
        {
          bvar_bindings = uu___1;
          fvar_bindings = (env.fvar_bindings);
          depth = (env.depth + Prims.int_one);
          tcenv = uu___2;
          warn = (env.warn);
          nolabels = (env.nolabels);
          use_zfuel_name = (env.use_zfuel_name);
          encode_non_total_function_typ = (env.encode_non_total_function_typ);
          current_module_name = (env.current_module_name);
          encoding_quantifier = (env.encoding_quantifier);
          global_cache = (env.global_cache)
        } in
      (ysym, y, uu___)
let (new_term_constant :
  env_t ->
    FStarC_Syntax_Syntax.bv ->
      (Prims.string * FStarC_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      let ysym =
        varops.new_var x.FStarC_Syntax_Syntax.ppname
          x.FStarC_Syntax_Syntax.index in
      let y = FStarC_SMTEncoding_Util.mkApp (ysym, []) in
      let uu___ =
        let uu___1 = add_bvar_binding (x, y) env.bvar_bindings in
        let uu___2 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
        {
          bvar_bindings = uu___1;
          fvar_bindings = (env.fvar_bindings);
          depth = (env.depth);
          tcenv = uu___2;
          warn = (env.warn);
          nolabels = (env.nolabels);
          use_zfuel_name = (env.use_zfuel_name);
          encode_non_total_function_typ = (env.encode_non_total_function_typ);
          current_module_name = (env.current_module_name);
          encoding_quantifier = (env.encoding_quantifier);
          global_cache = (env.global_cache)
        } in
      (ysym, y, uu___)
let (new_term_constant_from_string :
  env_t ->
    FStarC_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string * FStarC_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      fun str ->
        let ysym = varops.mk_unique str in
        let y = FStarC_SMTEncoding_Util.mkApp (ysym, []) in
        let uu___ =
          let uu___1 = add_bvar_binding (x, y) env.bvar_bindings in
          let uu___2 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
          {
            bvar_bindings = uu___1;
            fvar_bindings = (env.fvar_bindings);
            depth = (env.depth);
            tcenv = uu___2;
            warn = (env.warn);
            nolabels = (env.nolabels);
            use_zfuel_name = (env.use_zfuel_name);
            encode_non_total_function_typ =
              (env.encode_non_total_function_typ);
            current_module_name = (env.current_module_name);
            encoding_quantifier = (env.encoding_quantifier);
            global_cache = (env.global_cache)
          } in
        (ysym, y, uu___)
let (push_term_var :
  env_t -> FStarC_Syntax_Syntax.bv -> FStarC_SMTEncoding_Term.term -> env_t)
  =
  fun env ->
    fun x ->
      fun t ->
        let uu___ = add_bvar_binding (x, t) env.bvar_bindings in
        let uu___1 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
        {
          bvar_bindings = uu___;
          fvar_bindings = (env.fvar_bindings);
          depth = (env.depth);
          tcenv = uu___1;
          warn = (env.warn);
          nolabels = (env.nolabels);
          use_zfuel_name = (env.use_zfuel_name);
          encode_non_total_function_typ = (env.encode_non_total_function_typ);
          current_module_name = (env.current_module_name);
          encoding_quantifier = (env.encoding_quantifier);
          global_cache = (env.global_cache)
        }
let (lookup_term_var :
  env_t -> FStarC_Syntax_Syntax.bv -> FStarC_SMTEncoding_Term.term) =
  fun env ->
    fun a ->
      let uu___ = lookup_bvar_binding env a in
      match uu___ with
      | FStar_Pervasives_Native.Some (b, t) -> t
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv a in
            let uu___3 = print_env env in
            FStarC_Compiler_Util.format2
              "Bound term variable not found  %s in environment: %s" uu___2
              uu___3 in
          failwith uu___1
let (mk_fvb :
  FStarC_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term)
            FStar_Pervasives_Native.option -> Prims.bool -> fvar_binding)
  =
  fun lid ->
    fun fname ->
      fun arity ->
        fun ftok ->
          fun fuel_partial_app ->
            fun thunked ->
              let fvb =
                {
                  fvar_lid = lid;
                  smt_arity = arity;
                  smt_id = fname;
                  smt_token = ftok;
                  smt_fuel_partial_app = fuel_partial_app;
                  fvb_thunked = thunked
                } in
              check_valid_fvb fvb; fvb
let (new_term_constant_and_tok_from_lid_aux :
  env_t ->
    FStarC_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env ->
    fun x ->
      fun arity ->
        fun thunked ->
          let fname = varops.new_fvar x in
          let uu___ =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.strcat fname "@tok" in
               let ftok = FStarC_SMTEncoding_Util.mkApp (ftok_name, []) in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok))) in
          match uu___ with
          | (ftok_name, ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked in
              let uu___1 =
                let uu___2 = add_fvar_binding fvb env.fvar_bindings in
                {
                  bvar_bindings = (env.bvar_bindings);
                  fvar_bindings = uu___2;
                  depth = (env.depth);
                  tcenv = (env.tcenv);
                  warn = (env.warn);
                  nolabels = (env.nolabels);
                  use_zfuel_name = (env.use_zfuel_name);
                  encode_non_total_function_typ =
                    (env.encode_non_total_function_typ);
                  current_module_name = (env.current_module_name);
                  encoding_quantifier = (env.encoding_quantifier);
                  global_cache = (env.global_cache)
                } in
              (fname, ftok_name, uu___1)
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStarC_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env ->
    fun x ->
      fun arity ->
        let uu___ = new_term_constant_and_tok_from_lid_aux env x arity false in
        match uu___ with
        | (fname, ftok_name_opt, env1) ->
            let uu___1 = FStarC_Compiler_Option.get ftok_name_opt in
            (fname, uu___1, env1)
let (new_term_constant_and_tok_from_lid_maybe_thunked :
  env_t ->
    FStarC_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env ->
    fun x ->
      fun arity ->
        fun th -> new_term_constant_and_tok_from_lid_aux env x arity th
let fail_fvar_lookup : 'uuuuu . env_t -> FStarC_Ident.lident -> 'uuuuu =
  fun env ->
    fun a ->
      let q = FStarC_TypeChecker_Env.lookup_qname env.tcenv a in
      match q with
      | FStar_Pervasives_Native.None ->
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Ident.showable_lident a in
            FStarC_Compiler_Util.format1
              "Name %s not found in the smtencoding and typechecker env"
              uu___1 in
          failwith uu___
      | uu___ ->
          let quals = FStarC_TypeChecker_Env.quals_of_qninfo q in
          let uu___1 =
            (FStarC_Compiler_Util.is_some quals) &&
              (let uu___2 = FStarC_Compiler_Util.must quals in
               FStarC_Compiler_List.contains
                 FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen uu___2) in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Ident.showable_lident a in
              FStarC_Compiler_Util.format1
                "Name %s not found in the smtencoding env (the symbol is marked unfold, expected it to reduce)"
                uu___3 in
            FStarC_Errors.raise_error FStarC_Ident.hasrange_lident a
              FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2)
          else
            (let uu___3 =
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Ident.showable_lident a in
               FStarC_Compiler_Util.format1
                 "Name %s not found in the smtencoding env" uu___4 in
             failwith uu___3)
let (lookup_lid : env_t -> FStarC_Ident.lident -> fvar_binding) =
  fun env ->
    fun a ->
      let uu___ = lookup_fvar_binding env a in
      match uu___ with
      | FStar_Pervasives_Native.None -> fail_fvar_lookup env a
      | FStar_Pervasives_Native.Some s -> (check_valid_fvb s; s)
let (push_free_var_maybe_thunked :
  env_t ->
    FStarC_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            Prims.bool -> env_t)
  =
  fun env ->
    fun x ->
      fun arity ->
        fun fname ->
          fun ftok ->
            fun thunked ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked in
              let uu___ = add_fvar_binding fvb env.fvar_bindings in
              {
                bvar_bindings = (env.bvar_bindings);
                fvar_bindings = uu___;
                depth = (env.depth);
                tcenv = (env.tcenv);
                warn = (env.warn);
                nolabels = (env.nolabels);
                use_zfuel_name = (env.use_zfuel_name);
                encode_non_total_function_typ =
                  (env.encode_non_total_function_typ);
                current_module_name = (env.current_module_name);
                encoding_quantifier = (env.encoding_quantifier);
                global_cache = (env.global_cache)
              }
let (push_free_var :
  env_t ->
    FStarC_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            env_t)
  =
  fun env ->
    fun x ->
      fun arity ->
        fun fname ->
          fun ftok ->
            push_free_var_maybe_thunked env x arity fname ftok false
let (push_free_var_thunk :
  env_t ->
    FStarC_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            env_t)
  =
  fun env ->
    fun x ->
      fun arity ->
        fun fname ->
          fun ftok ->
            push_free_var_maybe_thunked env x arity fname ftok
              (arity = Prims.int_zero)
let (push_zfuel_name :
  env_t -> FStarC_Ident.lident -> Prims.string -> Prims.string -> env_t) =
  fun env ->
    fun x ->
      fun f ->
        fun ftok ->
          let fvb = lookup_lid env x in
          let t3 =
            let uu___ =
              let uu___1 =
                let uu___2 = FStarC_SMTEncoding_Util.mkApp ("ZFuel", []) in
                [uu___2] in
              (f, uu___1) in
            FStarC_SMTEncoding_Util.mkApp uu___ in
          let t3' =
            let uu___ = FStarC_SMTEncoding_Util.mkApp (ftok, []) in
            let uu___1 = FStarC_SMTEncoding_Util.mkApp ("ZFuel", []) in
            FStarC_SMTEncoding_Term.mk_ApplyTF uu___ uu___1 in
          let fvb1 =
            mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
              (FStar_Pervasives_Native.Some (t3, t3')) false in
          let uu___ = add_fvar_binding fvb1 env.fvar_bindings in
          {
            bvar_bindings = (env.bvar_bindings);
            fvar_bindings = uu___;
            depth = (env.depth);
            tcenv = (env.tcenv);
            warn = (env.warn);
            nolabels = (env.nolabels);
            use_zfuel_name = (env.use_zfuel_name);
            encode_non_total_function_typ =
              (env.encode_non_total_function_typ);
            current_module_name = (env.current_module_name);
            encoding_quantifier = (env.encoding_quantifier);
            global_cache = (env.global_cache)
          }
let (force_thunk : fvar_binding -> FStarC_SMTEncoding_Term.term) =
  fun fvb ->
    if
      (Prims.op_Negation fvb.fvb_thunked) ||
        (fvb.smt_arity <> Prims.int_zero)
    then failwith "Forcing a non-thunk in the SMT encoding"
    else ();
    FStarC_SMTEncoding_Util.mkFreeV
      (FStarC_SMTEncoding_Term.FV
         ((fvb.smt_id), FStarC_SMTEncoding_Term.Term_sort, true))
let (try_lookup_free_var :
  env_t ->
    FStarC_Ident.lident ->
      FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu___ = lookup_fvar_binding env l in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_PartialApp in
            if uu___2
            then
              let uu___3 = FStarC_Ident.string_of_lid l in
              let uu___4 = fvb_to_string fvb in
              FStarC_Compiler_Util.print2 "Looked up %s found\n%s\n" uu___3
                uu___4
            else ());
           if fvb.fvb_thunked
           then
             (let uu___2 = force_thunk fvb in
              FStar_Pervasives_Native.Some uu___2)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some (uu___3, f) when
                  env.use_zfuel_name -> FStar_Pervasives_Native.Some f
              | uu___3 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStarC_SMTEncoding_Term.tm with
                        | FStarC_SMTEncoding_Term.App (uu___4, fuel::[]) ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_SMTEncoding_Term.fv_of_term fuel in
                                FStarC_SMTEncoding_Term.fv_name uu___7 in
                              FStarC_Compiler_Util.starts_with uu___6 "fuel" in
                            if uu___5
                            then
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    FStarC_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStarC_SMTEncoding_Term.Term_sort) in
                                  FStarC_SMTEncoding_Util.mkFreeV uu___8 in
                                FStarC_SMTEncoding_Term.mk_ApplyTF uu___7
                                  fuel in
                              FStar_Pervasives_Native.Some uu___6
                            else FStar_Pervasives_Native.Some t
                        | uu___4 -> FStar_Pervasives_Native.Some t)
                   | uu___4 -> FStar_Pervasives_Native.None)))
let (lookup_free_var :
  env_t ->
    FStarC_Ident.lident FStarC_Syntax_Syntax.withinfo_t ->
      FStarC_SMTEncoding_Term.term)
  =
  fun env ->
    fun a ->
      let uu___ = try_lookup_free_var env a.FStarC_Syntax_Syntax.v in
      match uu___ with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          fail_fvar_lookup env a.FStarC_Syntax_Syntax.v
let (lookup_free_var_name :
  env_t ->
    FStarC_Ident.lident FStarC_Syntax_Syntax.withinfo_t -> fvar_binding)
  = fun env -> fun a -> lookup_lid env a.FStarC_Syntax_Syntax.v
let (lookup_free_var_sym :
  env_t ->
    FStarC_Ident.lident FStarC_Syntax_Syntax.withinfo_t ->
      ((FStarC_SMTEncoding_Term.op, FStarC_SMTEncoding_Term.term)
        FStar_Pervasives.either * FStarC_SMTEncoding_Term.term Prims.list *
        Prims.int))
  =
  fun env ->
    fun a ->
      let fvb = lookup_lid env a.FStarC_Syntax_Syntax.v in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          ({
             FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App (g, zf);
             FStarC_SMTEncoding_Term.freevars = uu___;
             FStarC_SMTEncoding_Term.rng = uu___1;_},
           uu___2)
          when env.use_zfuel_name ->
          ((FStar_Pervasives.Inl g), zf, (fvb.smt_arity + Prims.int_one))
      | uu___ ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None when fvb.fvb_thunked ->
               let uu___1 =
                 let uu___2 = force_thunk fvb in FStar_Pervasives.Inr uu___2 in
               (uu___1, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None ->
               ((FStar_Pervasives.Inl
                   (FStarC_SMTEncoding_Term.Var (fvb.smt_id))), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStarC_SMTEncoding_Term.tm with
                | FStarC_SMTEncoding_Term.App (g, fuel::[]) ->
                    ((FStar_Pervasives.Inl g), [fuel],
                      (fvb.smt_arity + Prims.int_one))
                | uu___1 ->
                    ((FStar_Pervasives.Inl
                        (FStarC_SMTEncoding_Term.Var (fvb.smt_id))), [],
                      (fvb.smt_arity))))
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun nm ->
      let uu___ =
        FStarC_Compiler_Util.psmap_find_map
          (FStar_Pervasives_Native.fst env.fvar_bindings)
          (fun uu___1 ->
             fun fvb ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None) in
      match uu___ with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None ->
          FStarC_Compiler_Util.psmap_find_map env.bvar_bindings
            (fun uu___1 ->
               fun pi ->
                 FStarC_Compiler_Util.pimap_fold pi
                   (fun uu___2 ->
                      fun y ->
                        fun res ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some uu___3, uu___4) ->
                              res
                          | (FStar_Pervasives_Native.None,
                             (uu___3,
                              {
                                FStarC_SMTEncoding_Term.tm =
                                  FStarC_SMTEncoding_Term.App
                                  (FStarC_SMTEncoding_Term.Var sym, []);
                                FStarC_SMTEncoding_Term.freevars = uu___4;
                                FStarC_SMTEncoding_Term.rng = uu___5;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu___3 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env ->
    {
      bvar_bindings = (env.bvar_bindings);
      fvar_bindings = ((FStar_Pervasives_Native.fst env.fvar_bindings), []);
      depth = (env.depth);
      tcenv = (env.tcenv);
      warn = (env.warn);
      nolabels = (env.nolabels);
      use_zfuel_name = (env.use_zfuel_name);
      encode_non_total_function_typ = (env.encode_non_total_function_typ);
      current_module_name = (env.current_module_name);
      encoding_quantifier = (env.encoding_quantifier);
      global_cache = (env.global_cache)
    }
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env -> FStar_Pervasives_Native.snd env.fvar_bindings
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb ->
    fun env ->
      let uu___ = add_fvar_binding fvb env.fvar_bindings in
      {
        bvar_bindings = (env.bvar_bindings);
        fvar_bindings = uu___;
        depth = (env.depth);
        tcenv = (env.tcenv);
        warn = (env.warn);
        nolabels = (env.nolabels);
        use_zfuel_name = (env.use_zfuel_name);
        encode_non_total_function_typ = (env.encode_non_total_function_typ);
        current_module_name = (env.current_module_name);
        encoding_quantifier = (env.encoding_quantifier);
        global_cache = (env.global_cache)
      }