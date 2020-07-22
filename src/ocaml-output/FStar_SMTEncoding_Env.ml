open Prims
exception Inner_let_rec of (Prims.string * FStar_Range.range) Prims.list 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Inner_let_rec uu____42 -> true | uu____49 -> false
let (__proj__Inner_let_rec__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) Prims.list) =
  fun projectee -> match projectee with | Inner_let_rec uu____67 -> uu____67
let add_fuel :
  'uuuuuu80 . 'uuuuuu80 -> 'uuuuuu80 Prims.list -> 'uuuuuu80 Prims.list =
  fun x ->
    fun tl ->
      let uu____97 = FStar_Options.unthrottle_inductives () in
      if uu____97 then tl else x :: tl
let withenv :
  'uuuuuu111 'uuuuuu112 'uuuuuu113 .
    'uuuuuu111 ->
      ('uuuuuu112 * 'uuuuuu113) -> ('uuuuuu112 * 'uuuuuu113 * 'uuuuuu111)
  = fun c -> fun uu____133 -> match uu____133 with | (a, b) -> (a, b, c)
let vargs :
  'uuuuuu148 'uuuuuu149 'uuuuuu150 .
    (('uuuuuu148, 'uuuuuu149) FStar_Util.either * 'uuuuuu150) Prims.list ->
      (('uuuuuu148, 'uuuuuu149) FStar_Util.either * 'uuuuuu150) Prims.list
  =
  fun args ->
    FStar_List.filter
      (fun uu___0_197 ->
         match uu___0_197 with
         | (FStar_Util.Inl uu____206, uu____207) -> false
         | uu____212 -> true) args
let (escape : Prims.string -> Prims.string) =
  fun s -> FStar_Util.replace_char s 39 95
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid ->
    fun a ->
      let uu____236 =
        let uu____237 = FStar_Ident.string_of_lid lid in
        let uu____238 = FStar_Ident.string_of_id a.FStar_Syntax_Syntax.ppname in
        FStar_Util.format2 "%s_%s" uu____237 uu____238 in
      FStar_All.pipe_left escape uu____236
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env ->
    fun lid ->
      fun i ->
        let fail uu____259 =
          let uu____260 =
            let uu____261 = FStar_Ident.string_of_lid lid in
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) uu____261 in
          failwith uu____260 in
        let uu____262 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____262 with
        | (uu____267, t) ->
            let uu____269 =
              let uu____270 = FStar_Syntax_Subst.compress t in
              uu____270.FStar_Syntax_Syntax.n in
            (match uu____269 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                 let uu____295 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____295 with
                  | (binders, uu____301) ->
                      if
                        (i < Prims.int_zero) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____324 -> fail ())
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid ->
    fun i ->
      let uu____335 =
        let uu____336 = FStar_Ident.string_of_lid lid in
        FStar_Util.format2 "%s_%s" uu____336 (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____335
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid ->
    fun a ->
      let uu____347 =
        let uu____348 =
          let uu____353 = mk_term_projector_name lid a in
          (uu____353,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort))) in
        FStar_SMTEncoding_Term.mk_fv uu____348 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____347
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid ->
    fun i ->
      let uu____364 =
        let uu____365 =
          let uu____370 = mk_term_projector_name_by_pos lid i in
          (uu____370,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort))) in
        FStar_SMTEncoding_Term.mk_fv uu____365 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____364
let mk_data_tester :
  'uuuuuu379 .
    'uuuuuu379 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env ->
    fun l ->
      fun x ->
        let uu____395 =
          let uu____396 = FStar_Ident.string_of_lid l in escape uu____396 in
        FStar_SMTEncoding_Term.mk_tester uu____395 x
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
  let new_scope uu____1190 = FStar_Util.smap_create (Prims.of_int (100)) in
  let scopes =
    let uu____1200 = let uu____1205 = new_scope () in [uu____1205] in
    FStar_Util.mk_ref uu____1200 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____1224 =
        let uu____1227 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____1227
          (fun names -> FStar_Util.smap_try_find names y1) in
      match uu____1224 with
      | FStar_Pervasives_Native.None -> y1
      | FStar_Pervasives_Native.Some uu____1252 ->
          (FStar_Util.incr ctr;
           (let uu____1254 =
              let uu____1255 =
                let uu____1256 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____1256 in
              Prims.op_Hat "__" uu____1255 in
            Prims.op_Hat y1 uu____1254)) in
    let top_scope =
      let uu____1266 = FStar_ST.op_Bang scopes in FStar_List.hd uu____1266 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    let uu____1299 =
      let uu____1300 = FStar_Ident.string_of_id pp in
      Prims.op_Hat uu____1300 (Prims.op_Hat "__" (Prims.string_of_int rn)) in
    FStar_All.pipe_left mk_unique uu____1299 in
  let new_fvar lid =
    let uu____1307 = FStar_Ident.string_of_lid lid in mk_unique uu____1307 in
  let next_id uu____1313 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh mname pfx =
    let uu____1332 =
      let uu____1333 = next_id () in
      FStar_All.pipe_left Prims.string_of_int uu____1333 in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____1332 in
  let reset_fresh uu____1339 = FStar_ST.op_Colon_Equals ctr initial_ctr in
  let push uu____1351 =
    let uu____1352 =
      let uu____1357 = new_scope () in
      let uu____1360 = FStar_ST.op_Bang scopes in uu____1357 :: uu____1360 in
    FStar_ST.op_Colon_Equals scopes uu____1352 in
  let pop uu____1400 =
    let uu____1401 =
      let uu____1406 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1406 in
    FStar_ST.op_Colon_Equals scopes uu____1401 in
  let snapshot uu____1450 = FStar_Common.snapshot push scopes () in
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
    let term_opt_to_string uu___1_1609 =
      match uu___1_1609 with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some s ->
          FStar_SMTEncoding_Term.print_smt_term s in
    let uu____1613 = FStar_Ident.string_of_lid fvb.fvar_lid in
    let uu____1614 = term_opt_to_string fvb.smt_token in
    let uu____1615 = term_opt_to_string fvb.smt_fuel_partial_app in
    let uu____1616 = FStar_Util.string_of_bool fvb.fvb_thunked in
    FStar_Util.format5
      "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
      uu____1613 fvb.smt_id uu____1614 uu____1615 uu____1616
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu____1623 =
         let uu____1624 = FStar_Ident.string_of_lid fvb.fvar_lid in
         FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____1624 in
       failwith uu____1623)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> Prims.int_zero)
      then
        (let uu____1626 =
           let uu____1627 = FStar_Ident.string_of_lid fvb.fvar_lid in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____1627 in
         failwith uu____1626)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         {
           FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
             uu____1629;
           FStar_SMTEncoding_Term.freevars = uu____1630;
           FStar_SMTEncoding_Term.rng = uu____1631;_}
         ->
         let uu____1648 =
           let uu____1649 = fvb_to_string fvb in
           FStar_Util.format1 "bad fvb\n%s" uu____1649 in
         failwith uu____1648
     | uu____1650 -> ())
let binder_of_eithervar :
  'uuuuuu1659 'uuuuuu1660 .
    'uuuuuu1659 -> ('uuuuuu1659 * 'uuuuuu1660 FStar_Pervasives_Native.option)
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
                    fun uu____2200 ->
                      fun acc1 ->
                        match uu____2200 with
                        | (x, _term) ->
                            let uu____2212 =
                              FStar_Syntax_Print.bv_to_string x in
                            uu____2212 :: acc1) acc) [] in
    let allvars =
      let uu____2216 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst in
      FStar_Util.psmap_fold uu____2216
        (fun _k -> fun fvb -> fun acc -> (fvb.fvar_lid) :: acc) [] in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____2245 ->
          let uu____2248 = FStar_Syntax_Print.lid_to_string l in
          Prims.op_Hat "...," uu____2248 in
    FStar_String.concat ", " (last_fvar :: bvars)
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun bv ->
      let uu____2265 =
        let uu____2274 =
          FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
        FStar_Util.psmap_try_find env.bvar_bindings uu____2274 in
      match uu____2265 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____2326 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst in
      let uu____2343 = FStar_Ident.string_of_lid lid in
      FStar_Util.psmap_try_find uu____2326 uu____2343
let add_bvar_binding :
  'uuuuuu2350 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu2350) ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu2350) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2350) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb ->
    fun bvbs ->
      let uu____2393 =
        FStar_Ident.string_of_id
          (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname in
      FStar_Util.psmap_modify bvbs uu____2393
        (fun pimap_opt ->
           let uu____2411 =
             let uu____2418 = FStar_Util.pimap_empty () in
             FStar_Util.dflt uu____2418 pimap_opt in
           FStar_Util.pimap_add uu____2411
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb ->
    fun uu____2464 ->
      match uu____2464 with
      | (fvb_map, fvb_list) ->
          let uu____2491 =
            let uu____2494 = FStar_Ident.string_of_lid fvb.fvar_lid in
            FStar_Util.psmap_add fvb_map uu____2494 fvb in
          (uu____2491, (fvb :: fvb_list))
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
        let uu____2519 =
          let uu____2520 = FStar_SMTEncoding_Term.mk_fv (xsym, s) in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____2520 in
        (xsym, uu____2519)
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env ->
    fun x ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth) in
      let y =
        let uu____2539 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort) in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____2539 in
      let uu____2540 =
        let uu___224_2541 = env in
        let uu____2542 = add_bvar_binding (x, y) env.bvar_bindings in
        {
          bvar_bindings = uu____2542;
          fvar_bindings = (uu___224_2541.fvar_bindings);
          depth = (env.depth + Prims.int_one);
          tcenv = (uu___224_2541.tcenv);
          warn = (uu___224_2541.warn);
          nolabels = (uu___224_2541.nolabels);
          use_zfuel_name = (uu___224_2541.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___224_2541.encode_non_total_function_typ);
          current_module_name = (uu___224_2541.current_module_name);
          encoding_quantifier = (uu___224_2541.encoding_quantifier);
          global_cache = (uu___224_2541.global_cache)
        } in
      (ysym, y, uu____2540)
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
      let uu____2571 =
        let uu___230_2572 = env in
        let uu____2573 = add_bvar_binding (x, y) env.bvar_bindings in
        {
          bvar_bindings = uu____2573;
          fvar_bindings = (uu___230_2572.fvar_bindings);
          depth = (uu___230_2572.depth);
          tcenv = (uu___230_2572.tcenv);
          warn = (uu___230_2572.warn);
          nolabels = (uu___230_2572.nolabels);
          use_zfuel_name = (uu___230_2572.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___230_2572.encode_non_total_function_typ);
          current_module_name = (uu___230_2572.current_module_name);
          encoding_quantifier = (uu___230_2572.encoding_quantifier);
          global_cache = (uu___230_2572.global_cache)
        } in
      (ysym, y, uu____2571)
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
        let uu____2607 =
          let uu___237_2608 = env in
          let uu____2609 = add_bvar_binding (x, y) env.bvar_bindings in
          {
            bvar_bindings = uu____2609;
            fvar_bindings = (uu___237_2608.fvar_bindings);
            depth = (uu___237_2608.depth);
            tcenv = (uu___237_2608.tcenv);
            warn = (uu___237_2608.warn);
            nolabels = (uu___237_2608.nolabels);
            use_zfuel_name = (uu___237_2608.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___237_2608.encode_non_total_function_typ);
            current_module_name = (uu___237_2608.current_module_name);
            encoding_quantifier = (uu___237_2608.encoding_quantifier);
            global_cache = (uu___237_2608.global_cache)
          } in
        (ysym, y, uu____2607)
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env ->
    fun x ->
      fun t ->
        let uu___242_2633 = env in
        let uu____2634 = add_bvar_binding (x, t) env.bvar_bindings in
        {
          bvar_bindings = uu____2634;
          fvar_bindings = (uu___242_2633.fvar_bindings);
          depth = (uu___242_2633.depth);
          tcenv = (uu___242_2633.tcenv);
          warn = (uu___242_2633.warn);
          nolabels = (uu___242_2633.nolabels);
          use_zfuel_name = (uu___242_2633.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___242_2633.encode_non_total_function_typ);
          current_module_name = (uu___242_2633.current_module_name);
          encoding_quantifier = (uu___242_2633.encoding_quantifier);
          global_cache = (uu___242_2633.global_cache)
        }
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env ->
    fun a ->
      let uu____2653 = lookup_bvar_binding env a in
      match uu____2653 with
      | FStar_Pervasives_Native.None ->
          let uu____2664 = lookup_bvar_binding env a in
          (match uu____2664 with
           | FStar_Pervasives_Native.None ->
               let uu____2675 =
                 let uu____2676 = FStar_Syntax_Print.bv_to_string a in
                 let uu____2677 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____2676 uu____2677 in
               failwith uu____2675
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
          let uu____2759 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok" in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, []) in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok))) in
          match uu____2759 with
          | (ftok_name, ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked in
              let uu____2808 =
                let uu___276_2809 = env in
                let uu____2810 = add_fvar_binding fvb env.fvar_bindings in
                {
                  bvar_bindings = (uu___276_2809.bvar_bindings);
                  fvar_bindings = uu____2810;
                  depth = (uu___276_2809.depth);
                  tcenv = (uu___276_2809.tcenv);
                  warn = (uu___276_2809.warn);
                  nolabels = (uu___276_2809.nolabels);
                  use_zfuel_name = (uu___276_2809.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___276_2809.encode_non_total_function_typ);
                  current_module_name = (uu___276_2809.current_module_name);
                  encoding_quantifier = (uu___276_2809.encoding_quantifier);
                  global_cache = (uu___276_2809.global_cache)
                } in
              (fname, ftok_name, uu____2808)
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env ->
    fun x ->
      fun arity ->
        let uu____2842 =
          new_term_constant_and_tok_from_lid_aux env x arity false in
        match uu____2842 with
        | (fname, ftok_name_opt, env1) ->
            let uu____2864 = FStar_Option.get ftok_name_opt in
            (fname, uu____2864, env1)
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
      let uu____2903 = lookup_fvar_binding env a in
      match uu____2903 with
      | FStar_Pervasives_Native.None ->
          let uu____2906 =
            let uu____2907 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2907 in
          failwith uu____2906
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
              let uu___302_2945 = env in
              let uu____2946 = add_fvar_binding fvb env.fvar_bindings in
              {
                bvar_bindings = (uu___302_2945.bvar_bindings);
                fvar_bindings = uu____2946;
                depth = (uu___302_2945.depth);
                tcenv = (uu___302_2945.tcenv);
                warn = (uu___302_2945.warn);
                nolabels = (uu___302_2945.nolabels);
                use_zfuel_name = (uu___302_2945.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___302_2945.encode_non_total_function_typ);
                current_module_name = (uu___302_2945.current_module_name);
                encoding_quantifier = (uu___302_2945.encoding_quantifier);
                global_cache = (uu___302_2945.global_cache)
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
          let uu____3030 =
            let uu____3037 =
              let uu____3040 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
              [uu____3040] in
            (f, uu____3037) in
          FStar_SMTEncoding_Util.mkApp uu____3030 in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false in
        let uu___320_3046 = env in
        let uu____3047 = add_fvar_binding fvb1 env.fvar_bindings in
        {
          bvar_bindings = (uu___320_3046.bvar_bindings);
          fvar_bindings = uu____3047;
          depth = (uu___320_3046.depth);
          tcenv = (uu___320_3046.tcenv);
          warn = (uu___320_3046.warn);
          nolabels = (uu___320_3046.nolabels);
          use_zfuel_name = (uu___320_3046.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___320_3046.encode_non_total_function_typ);
          current_module_name = (uu___320_3046.current_module_name);
          encoding_quantifier = (uu___320_3046.encoding_quantifier);
          global_cache = (uu___320_3046.global_cache)
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
      let uu____3075 = lookup_fvar_binding env l in
      match uu____3075 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu____3082 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
                (FStar_Options.Other "PartialApp") in
            if uu____3082
            then
              let uu____3083 = FStar_Ident.string_of_lid l in
              let uu____3084 = fvb_to_string fvb in
              FStar_Util.print2 "Looked up %s found\n%s\n" uu____3083
                uu____3084
            else ());
           if fvb.fvb_thunked
           then
             (let uu____3088 = force_thunk fvb in
              FStar_Pervasives_Native.Some uu____3088)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                  FStar_Pervasives_Native.Some f
              | uu____3093 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App (uu____3101, fuel::[])
                            ->
                            let uu____3105 =
                              let uu____3106 =
                                let uu____3107 =
                                  FStar_SMTEncoding_Term.fv_of_term fuel in
                                FStar_All.pipe_right uu____3107
                                  FStar_SMTEncoding_Term.fv_name in
                              FStar_Util.starts_with uu____3106 "fuel" in
                            if uu____3105
                            then
                              let uu____3110 =
                                let uu____3111 =
                                  let uu____3112 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStar_SMTEncoding_Term.Term_sort) in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Util.mkFreeV uu____3112 in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____3111
                                  fuel in
                              FStar_All.pipe_left
                                (fun uu____3115 ->
                                   FStar_Pervasives_Native.Some uu____3115)
                                uu____3110
                            else FStar_Pervasives_Native.Some t
                        | uu____3117 -> FStar_Pervasives_Native.Some t)
                   | uu____3118 -> FStar_Pervasives_Native.None)))
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env ->
    fun a ->
      let uu____3135 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____3135 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let uu____3139 =
            let uu____3140 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3140 in
          failwith uu____3139
let (lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> fvar_binding)
  = fun env -> fun a -> lookup_lid env a.FStar_Syntax_Syntax.v
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      ((FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term)
        FStar_Util.either * FStar_SMTEncoding_Term.term Prims.list *
        Prims.int))
  =
  fun env ->
    fun a ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf);
            FStar_SMTEncoding_Term.freevars = uu____3196;
            FStar_SMTEncoding_Term.rng = uu____3197;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + Prims.int_one))
      | uu____3218 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None when fvb.fvb_thunked ->
               let uu____3233 =
                 let uu____3238 = force_thunk fvb in
                 FStar_Util.Inr uu____3238 in
               (uu____3233, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g, fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + Prims.int_one))
                | uu____3274 ->
                    ((FStar_Util.Inl
                        (FStar_SMTEncoding_Term.Var (fvb.smt_id))), [],
                      (fvb.smt_arity))))
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun nm ->
      let uu____3293 =
        let uu____3296 =
          FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst in
        FStar_Util.psmap_find_map uu____3296
          (fun uu____3316 ->
             fun fvb ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None) in
      match uu____3293 with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None ->
          FStar_Util.psmap_find_map env.bvar_bindings
            (fun uu____3333 ->
               fun pi ->
                 FStar_Util.pimap_fold pi
                   (fun uu____3352 ->
                      fun y ->
                        fun res ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some uu____3369,
                             uu____3370) -> res
                          | (FStar_Pervasives_Native.None,
                             (uu____3381,
                              {
                                FStar_SMTEncoding_Term.tm =
                                  FStar_SMTEncoding_Term.App
                                  (FStar_SMTEncoding_Term.Var sym, []);
                                FStar_SMTEncoding_Term.freevars = uu____3383;
                                FStar_SMTEncoding_Term.rng = uu____3384;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu____3403 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env ->
    let uu___407_3419 = env in
    let uu____3420 =
      let uu____3429 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst in
      (uu____3429, []) in
    {
      bvar_bindings = (uu___407_3419.bvar_bindings);
      fvar_bindings = uu____3420;
      depth = (uu___407_3419.depth);
      tcenv = (uu___407_3419.tcenv);
      warn = (uu___407_3419.warn);
      nolabels = (uu___407_3419.nolabels);
      use_zfuel_name = (uu___407_3419.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___407_3419.encode_non_total_function_typ);
      current_module_name = (uu___407_3419.current_module_name);
      encoding_quantifier = (uu___407_3419.encoding_quantifier);
      global_cache = (uu___407_3419.global_cache)
    }
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb ->
    fun env ->
      let uu___412_3481 = env in
      let uu____3482 = add_fvar_binding fvb env.fvar_bindings in
      {
        bvar_bindings = (uu___412_3481.bvar_bindings);
        fvar_bindings = uu____3482;
        depth = (uu___412_3481.depth);
        tcenv = (uu___412_3481.tcenv);
        warn = (uu___412_3481.warn);
        nolabels = (uu___412_3481.nolabels);
        use_zfuel_name = (uu___412_3481.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___412_3481.encode_non_total_function_typ);
        current_module_name = (uu___412_3481.current_module_name);
        encoding_quantifier = (uu___412_3481.encoding_quantifier);
        global_cache = (uu___412_3481.global_cache)
      }