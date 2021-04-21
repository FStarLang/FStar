open Prims
exception Inner_let_rec of (Prims.string * FStar_Range.range) Prims.list 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Inner_let_rec uu___ -> true | uu___ -> false
let (__proj__Inner_let_rec__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) Prims.list) =
  fun projectee -> match projectee with | Inner_let_rec uu___ -> uu___
let add_fuel : 'uuuuu . 'uuuuu -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun x ->
    fun tl ->
      let uu___ = FStar_Options.unthrottle_inductives () in
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
    FStar_List.filter
      (fun uu___ ->
         match uu___ with
         | (FStar_Pervasives.Inl uu___1, uu___2) -> false
         | uu___1 -> true) args
let (escape : Prims.string -> Prims.string) =
  fun s -> FStar_Util.replace_char s 39 95
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid ->
    fun a ->
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid lid in
        let uu___2 = FStar_Ident.string_of_id a.FStar_Syntax_Syntax.ppname in
        FStar_Util.format2 "%s_%s" uu___1 uu___2 in
      FStar_All.pipe_left escape uu___
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env ->
    fun lid ->
      fun i ->
        let fail uu___ =
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid lid in
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) uu___2 in
          failwith uu___1 in
        let uu___ = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu___ with
        | (uu___1, t) ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Subst.compress t in
              uu___3.FStar_Syntax_Syntax.n in
            (match uu___2 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                 let uu___3 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu___3 with
                  | (binders, uu___4) ->
                      if
                        (i < Prims.int_zero) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           b.FStar_Syntax_Syntax.binder_bv))
             | uu___3 -> fail ())
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid ->
    fun i ->
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid lid in
        FStar_Util.format2 "%s_%s" uu___1 (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu___
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid ->
    fun a ->
      let uu___ =
        let uu___1 =
          let uu___2 = mk_term_projector_name lid a in
          (uu___2,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort))) in
        FStar_SMTEncoding_Term.mk_fv uu___1 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid ->
    fun i ->
      let uu___ =
        let uu___1 =
          let uu___2 = mk_term_projector_name_by_pos lid i in
          (uu___2,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort))) in
        FStar_SMTEncoding_Term.mk_fv uu___1 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___
let mk_data_tester :
  'uuuuu .
    'uuuuu ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env ->
    fun l ->
      fun x ->
        let uu___ = let uu___1 = FStar_Ident.string_of_lid l in escape uu___1 in
        FStar_SMTEncoding_Term.mk_tester uu___ x
type varops_t =
  {
  push: unit -> unit ;
  pop: unit -> unit ;
  snapshot: unit -> (Prims.int * unit) ;
  rollback: Prims.int FStar_Pervasives_Native.option -> unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
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
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> new_var
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
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
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu___ = FStar_Util.smap_create (Prims.of_int (100)) in
  let scopes =
    let uu___ = let uu___1 = new_scope () in [uu___1] in
    FStar_Util.mk_ref uu___ in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu___ =
        let uu___1 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu___1
          (fun names -> FStar_Util.smap_try_find names y1) in
      match uu___ with
      | FStar_Pervasives_Native.None -> y1
      | FStar_Pervasives_Native.Some uu___1 ->
          (FStar_Util.incr ctr;
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu___5 in
              Prims.op_Hat "__" uu___4 in
            Prims.op_Hat y1 uu___3)) in
    let top_scope =
      let uu___ = FStar_ST.op_Bang scopes in FStar_List.hd uu___ in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    let uu___ =
      let uu___1 = FStar_Ident.string_of_id pp in
      Prims.op_Hat uu___1 (Prims.op_Hat "__" (Prims.string_of_int rn)) in
    FStar_All.pipe_left mk_unique uu___ in
  let new_fvar lid =
    let uu___ = FStar_Ident.string_of_lid lid in mk_unique uu___ in
  let next_id uu___ = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh mname pfx =
    let uu___ =
      let uu___1 = next_id () in
      FStar_All.pipe_left Prims.string_of_int uu___1 in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu___ in
  let reset_fresh uu___ = FStar_ST.op_Colon_Equals ctr initial_ctr in
  let push uu___ =
    let uu___1 =
      let uu___2 = new_scope () in
      let uu___3 = FStar_ST.op_Bang scopes in uu___2 :: uu___3 in
    FStar_ST.op_Colon_Equals scopes uu___1 in
  let pop uu___ =
    let uu___1 = let uu___2 = FStar_ST.op_Bang scopes in FStar_List.tl uu___2 in
    FStar_ST.op_Colon_Equals scopes uu___1 in
  let snapshot uu___ = FStar_Common.snapshot push scopes () in
  let rollback depth = FStar_Common.rollback pop scopes depth in
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
  fvar_lid: FStar_Ident.lident ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  fvb_thunked: Prims.bool }
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
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
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_token
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
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
          FStar_SMTEncoding_Term.print_smt_term s in
    let uu___ = FStar_Ident.string_of_lid fvb.fvar_lid in
    let uu___1 = term_opt_to_string fvb.smt_token in
    let uu___2 = term_opt_to_string fvb.smt_fuel_partial_app in
    let uu___3 = FStar_Util.string_of_bool fvb.fvb_thunked in
    FStar_Util.format5
      "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
      uu___ fvb.smt_id uu___1 uu___2 uu___3
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu___1 =
         let uu___2 = FStar_Ident.string_of_lid fvb.fvar_lid in
         FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu___2 in
       failwith uu___1)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> Prims.int_zero)
      then
        (let uu___2 =
           let uu___3 = FStar_Ident.string_of_lid fvb.fvar_lid in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu___3 in
         failwith uu___2)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV uu___1;
           FStar_SMTEncoding_Term.freevars = uu___2;
           FStar_SMTEncoding_Term.rng = uu___3;_}
         ->
         let uu___4 =
           let uu___5 = fvb_to_string fvb in
           FStar_Util.format1 "bad fvb\n%s" uu___5 in
         failwith uu___4
     | uu___1 -> ())
let binder_of_eithervar :
  'uuuuu 'uuuuu1 .
    'uuuuu -> ('uuuuu * 'uuuuu1 FStar_Pervasives_Native.option)
  = fun v -> (v, FStar_Pervasives_Native.None)
type env_t =
  {
  bvar_bindings:
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap
    ;
  fvar_bindings: (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string ;
  encoding_quantifier: Prims.bool ;
  global_cache: FStar_SMTEncoding_Term.decls_elt FStar_Util.smap }
let (__proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> bvar_bindings
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> (fvar_binding FStar_Util.psmap * fvar_binding Prims.list)) =
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
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
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
  env_t -> FStar_SMTEncoding_Term.decls_elt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> global_cache
let (print_env : env_t -> Prims.string) =
  fun e ->
    let bvars =
      FStar_Util.psmap_fold e.bvar_bindings
        (fun _k ->
           fun pi ->
             fun acc ->
               FStar_Util.pimap_fold pi
                 (fun _i ->
                    fun uu___ ->
                      fun acc1 ->
                        match uu___ with
                        | (x, _term) ->
                            let uu___1 = FStar_Syntax_Print.bv_to_string x in
                            uu___1 :: acc1) acc) [] in
    let allvars =
      let uu___ =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst in
      FStar_Util.psmap_fold uu___
        (fun _k -> fun fvb -> fun acc -> (fvb.fvar_lid) :: acc) [] in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu___ ->
          let uu___1 = FStar_Syntax_Print.lid_to_string l in
          Prims.op_Hat "...," uu___1 in
    FStar_String.concat ", " (last_fvar :: bvars)
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun bv ->
      let uu___ =
        let uu___1 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
        FStar_Util.psmap_try_find env.bvar_bindings uu___1 in
      match uu___ with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu___ =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst in
      let uu___1 = FStar_Ident.string_of_lid lid in
      FStar_Util.psmap_try_find uu___ uu___1
let add_bvar_binding :
  'uuuuu .
    (FStar_Syntax_Syntax.bv * 'uuuuu) ->
      (FStar_Syntax_Syntax.bv * 'uuuuu) FStar_Util.pimap FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'uuuuu) FStar_Util.pimap FStar_Util.psmap
  =
  fun bvb ->
    fun bvbs ->
      let uu___ =
        FStar_Ident.string_of_id
          (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname in
      FStar_Util.psmap_modify bvbs uu___
        (fun pimap_opt ->
           let uu___1 =
             let uu___2 = FStar_Util.pimap_empty () in
             FStar_Util.dflt uu___2 pimap_opt in
           FStar_Util.pimap_add uu___1
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb ->
    fun uu___ ->
      match uu___ with
      | (fvb_map, fvb_list) ->
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid fvb.fvar_lid in
            FStar_Util.psmap_add fvb_map uu___2 fvb in
          (uu___1, (fvb :: fvb_list))
let (fresh_fvar :
  Prims.string ->
    Prims.string ->
      FStar_SMTEncoding_Term.sort ->
        (Prims.string * FStar_SMTEncoding_Term.term))
  =
  fun mname ->
    fun x ->
      fun s ->
        let xsym = varops.fresh mname x in
        let uu___ =
          let uu___1 = FStar_SMTEncoding_Term.mk_fv (xsym, s) in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___1 in
        (xsym, uu___)
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth) in
      let y =
        let uu___ =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort) in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___ in
      let uu___ =
        let uu___1 = env in
        let uu___2 = add_bvar_binding (x, y) env.bvar_bindings in
        {
          bvar_bindings = uu___2;
          fvar_bindings = (uu___1.fvar_bindings);
          depth = (env.depth + Prims.int_one);
          tcenv = (uu___1.tcenv);
          warn = (uu___1.warn);
          nolabels = (uu___1.nolabels);
          use_zfuel_name = (uu___1.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___1.encode_non_total_function_typ);
          current_module_name = (uu___1.current_module_name);
          encoding_quantifier = (uu___1.encoding_quantifier);
          global_cache = (uu___1.global_cache)
        } in
      (ysym, y, uu___)
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      let uu___ =
        let uu___1 = env in
        let uu___2 = add_bvar_binding (x, y) env.bvar_bindings in
        {
          bvar_bindings = uu___2;
          fvar_bindings = (uu___1.fvar_bindings);
          depth = (uu___1.depth);
          tcenv = (uu___1.tcenv);
          warn = (uu___1.warn);
          nolabels = (uu___1.nolabels);
          use_zfuel_name = (uu___1.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___1.encode_non_total_function_typ);
          current_module_name = (uu___1.current_module_name);
          encoding_quantifier = (uu___1.encoding_quantifier);
          global_cache = (uu___1.global_cache)
        } in
      (ysym, y, uu___)
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      fun str ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        let uu___ =
          let uu___1 = env in
          let uu___2 = add_bvar_binding (x, y) env.bvar_bindings in
          {
            bvar_bindings = uu___2;
            fvar_bindings = (uu___1.fvar_bindings);
            depth = (uu___1.depth);
            tcenv = (uu___1.tcenv);
            warn = (uu___1.warn);
            nolabels = (uu___1.nolabels);
            use_zfuel_name = (uu___1.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___1.encode_non_total_function_typ);
            current_module_name = (uu___1.current_module_name);
            encoding_quantifier = (uu___1.encoding_quantifier);
            global_cache = (uu___1.global_cache)
          } in
        (ysym, y, uu___)
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env ->
    fun x ->
      fun t ->
        let uu___ = env in
        let uu___1 = add_bvar_binding (x, t) env.bvar_bindings in
        {
          bvar_bindings = uu___1;
          fvar_bindings = (uu___.fvar_bindings);
          depth = (uu___.depth);
          tcenv = (uu___.tcenv);
          warn = (uu___.warn);
          nolabels = (uu___.nolabels);
          use_zfuel_name = (uu___.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___.encode_non_total_function_typ);
          current_module_name = (uu___.current_module_name);
          encoding_quantifier = (uu___.encoding_quantifier);
          global_cache = (uu___.global_cache)
        }
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env ->
    fun a ->
      let uu___ = lookup_bvar_binding env a in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 = lookup_bvar_binding env a in
          (match uu___1 with
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Print.bv_to_string a in
                 let uu___4 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu___3 uu___4 in
               failwith uu___2
           | FStar_Pervasives_Native.Some (b, t) -> t)
      | FStar_Pervasives_Native.Some (b, t) -> t
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            Prims.bool -> fvar_binding)
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
    FStar_Ident.lident ->
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
              (let ftok_name = Prims.op_Hat fname "@tok" in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, []) in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok))) in
          match uu___ with
          | (ftok_name, ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked in
              let uu___1 =
                let uu___2 = env in
                let uu___3 = add_fvar_binding fvb env.fvar_bindings in
                {
                  bvar_bindings = (uu___2.bvar_bindings);
                  fvar_bindings = uu___3;
                  depth = (uu___2.depth);
                  tcenv = (uu___2.tcenv);
                  warn = (uu___2.warn);
                  nolabels = (uu___2.nolabels);
                  use_zfuel_name = (uu___2.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___2.encode_non_total_function_typ);
                  current_module_name = (uu___2.current_module_name);
                  encoding_quantifier = (uu___2.encoding_quantifier);
                  global_cache = (uu___2.global_cache)
                } in
              (fname, ftok_name, uu___1)
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env ->
    fun x ->
      fun arity ->
        let uu___ = new_term_constant_and_tok_from_lid_aux env x arity false in
        match uu___ with
        | (fname, ftok_name_opt, env1) ->
            let uu___1 = FStar_Option.get ftok_name_opt in
            (fname, uu___1, env1)
let (new_term_constant_and_tok_from_lid_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env ->
    fun x ->
      fun arity ->
        fun th -> new_term_constant_and_tok_from_lid_aux env x arity th
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env ->
    fun a ->
      let uu___ = lookup_fvar_binding env a in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu___2 in
          failwith uu___1
      | FStar_Pervasives_Native.Some s -> (check_valid_fvb s; s)
let (push_free_var_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
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
              let uu___ = env in
              let uu___1 = add_fvar_binding fvb env.fvar_bindings in
              {
                bvar_bindings = (uu___.bvar_bindings);
                fvar_bindings = uu___1;
                depth = (uu___.depth);
                tcenv = (uu___.tcenv);
                warn = (uu___.warn);
                nolabels = (uu___.nolabels);
                use_zfuel_name = (uu___.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___.encode_non_total_function_typ);
                current_module_name = (uu___.current_module_name);
                encoding_quantifier = (uu___.encoding_quantifier);
                global_cache = (uu___.global_cache)
              }
let (push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env ->
    fun x ->
      fun arity ->
        fun fname ->
          fun ftok ->
            push_free_var_maybe_thunked env x arity fname ftok false
let (push_free_var_thunk :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env ->
    fun x ->
      fun arity ->
        fun fname ->
          fun ftok ->
            push_free_var_maybe_thunked env x arity fname ftok
              (arity = Prims.int_zero)
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env ->
    fun x ->
      fun f ->
        let fvb = lookup_lid env x in
        let t3 =
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
              [uu___2] in
            (f, uu___1) in
          FStar_SMTEncoding_Util.mkApp uu___ in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false in
        let uu___ = env in
        let uu___1 = add_fvar_binding fvb1 env.fvar_bindings in
        {
          bvar_bindings = (uu___.bvar_bindings);
          fvar_bindings = uu___1;
          depth = (uu___.depth);
          tcenv = (uu___.tcenv);
          warn = (uu___.warn);
          nolabels = (uu___.nolabels);
          use_zfuel_name = (uu___.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___.encode_non_total_function_typ);
          current_module_name = (uu___.current_module_name);
          encoding_quantifier = (uu___.encoding_quantifier);
          global_cache = (uu___.global_cache)
        }
let (force_thunk : fvar_binding -> FStar_SMTEncoding_Term.term) =
  fun fvb ->
    if
      (Prims.op_Negation fvb.fvb_thunked) ||
        (fvb.smt_arity <> Prims.int_zero)
    then failwith "Forcing a non-thunk in the SMT encoding"
    else ();
    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
      ((fvb.smt_id), FStar_SMTEncoding_Term.Term_sort, true)
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu___ = lookup_fvar_binding env l in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu___2 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
                (FStar_Options.Other "PartialApp") in
            if uu___2
            then
              let uu___3 = FStar_Ident.string_of_lid l in
              let uu___4 = fvb_to_string fvb in
              FStar_Util.print2 "Looked up %s found\n%s\n" uu___3 uu___4
            else ());
           if fvb.fvb_thunked
           then
             (let uu___2 = force_thunk fvb in
              FStar_Pervasives_Native.Some uu___2)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                  FStar_Pervasives_Native.Some f
              | uu___3 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App (uu___4, fuel::[]) ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_SMTEncoding_Term.fv_of_term fuel in
                                FStar_All.pipe_right uu___7
                                  FStar_SMTEncoding_Term.fv_name in
                              FStar_Util.starts_with uu___6 "fuel" in
                            if uu___5
                            then
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStar_SMTEncoding_Term.Term_sort) in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Util.mkFreeV uu___8 in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu___7 fuel in
                              FStar_All.pipe_left
                                (fun uu___7 ->
                                   FStar_Pervasives_Native.Some uu___7)
                                uu___6
                            else FStar_Pervasives_Native.Some t
                        | uu___4 -> FStar_Pervasives_Native.Some t)
                   | uu___4 -> FStar_Pervasives_Native.None)))
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env ->
    fun a ->
      let uu___ = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu___ with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu___2 in
          failwith uu___1
let (lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> fvar_binding)
  = fun env -> fun a -> lookup_lid env a.FStar_Syntax_Syntax.v
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      ((FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term)
        FStar_Pervasives.either * FStar_SMTEncoding_Term.term Prims.list *
        Prims.int))
  =
  fun env ->
    fun a ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf);
            FStar_SMTEncoding_Term.freevars = uu___;
            FStar_SMTEncoding_Term.rng = uu___1;_}
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
                   (FStar_SMTEncoding_Term.Var (fvb.smt_id))), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g, fuel::[]) ->
                    ((FStar_Pervasives.Inl g), [fuel],
                      (fvb.smt_arity + Prims.int_one))
                | uu___1 ->
                    ((FStar_Pervasives.Inl
                        (FStar_SMTEncoding_Term.Var (fvb.smt_id))), [],
                      (fvb.smt_arity))))
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun nm ->
      let uu___ =
        let uu___1 =
          FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst in
        FStar_Util.psmap_find_map uu___1
          (fun uu___2 ->
             fun fvb ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None) in
      match uu___ with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None ->
          FStar_Util.psmap_find_map env.bvar_bindings
            (fun uu___1 ->
               fun pi ->
                 FStar_Util.pimap_fold pi
                   (fun uu___2 ->
                      fun y ->
                        fun res ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some uu___3, uu___4) ->
                              res
                          | (FStar_Pervasives_Native.None,
                             (uu___3,
                              {
                                FStar_SMTEncoding_Term.tm =
                                  FStar_SMTEncoding_Term.App
                                  (FStar_SMTEncoding_Term.Var sym, []);
                                FStar_SMTEncoding_Term.freevars = uu___4;
                                FStar_SMTEncoding_Term.rng = uu___5;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu___3 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env ->
    let uu___ = env in
    let uu___1 =
      let uu___2 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst in
      (uu___2, []) in
    {
      bvar_bindings = (uu___.bvar_bindings);
      fvar_bindings = uu___1;
      depth = (uu___.depth);
      tcenv = (uu___.tcenv);
      warn = (uu___.warn);
      nolabels = (uu___.nolabels);
      use_zfuel_name = (uu___.use_zfuel_name);
      encode_non_total_function_typ = (uu___.encode_non_total_function_typ);
      current_module_name = (uu___.current_module_name);
      encoding_quantifier = (uu___.encoding_quantifier);
      global_cache = (uu___.global_cache)
    }
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb ->
    fun env ->
      let uu___ = env in
      let uu___1 = add_fvar_binding fvb env.fvar_bindings in
      {
        bvar_bindings = (uu___.bvar_bindings);
        fvar_bindings = uu___1;
        depth = (uu___.depth);
        tcenv = (uu___.tcenv);
        warn = (uu___.warn);
        nolabels = (uu___.nolabels);
        use_zfuel_name = (uu___.use_zfuel_name);
        encode_non_total_function_typ = (uu___.encode_non_total_function_typ);
        current_module_name = (uu___.current_module_name);
        encoding_quantifier = (uu___.encoding_quantifier);
        global_cache = (uu___.global_cache)
      }