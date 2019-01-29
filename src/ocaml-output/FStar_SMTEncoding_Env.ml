open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____9 -> false
  
let add_fuel :
  'Auu____18 . 'Auu____18 -> 'Auu____18 Prims.list -> 'Auu____18 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____35 = FStar_Options.unthrottle_inductives ()  in
      if uu____35 then tl1 else x :: tl1
  
let withenv :
  'Auu____53 'Auu____54 'Auu____55 .
    'Auu____53 ->
      ('Auu____54 * 'Auu____55) -> ('Auu____54 * 'Auu____55 * 'Auu____53)
  = fun c  -> fun uu____75  -> match uu____75 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____91 'Auu____92 'Auu____93 .
    (('Auu____91,'Auu____92) FStar_Util.either * 'Auu____93) Prims.list ->
      (('Auu____91,'Auu____92) FStar_Util.either * 'Auu____93) Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___267_140  ->
         match uu___267_140 with
         | (FStar_Util.Inl uu____150,uu____151) -> false
         | uu____157 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____190 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____190
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____220 =
          let uu____221 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____221  in
        let uu____225 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____225 with
        | (uu____231,t) ->
            let uu____233 =
              let uu____234 = FStar_Syntax_Subst.compress t  in
              uu____234.FStar_Syntax_Syntax.n  in
            (match uu____233 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____260 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____260 with
                  | (binders,uu____267) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____294 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____309 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____309
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____325 =
        let uu____331 = mk_term_projector_name lid a  in
        (uu____331,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____325
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____347 =
        let uu____353 = mk_term_projector_name_by_pos lid i  in
        (uu____353,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____347
  
let mk_data_tester :
  'Auu____365 .
    'Auu____365 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
type varops_t =
  {
  push: unit -> unit ;
  pop: unit -> unit ;
  snapshot: unit -> (Prims.int * unit) ;
  rollback: Prims.int FStar_Pervasives_Native.option -> unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let (__proj__Mkvarops_t__item__push : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> push1
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> pop1
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int * unit)) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> snapshot1
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> rollback1
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> fresh1
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> next_id1
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1297 =
    let uu____1298 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1304 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1298, uu____1304)  in
  let scopes =
    let uu____1327 = let uu____1339 = new_scope ()  in [uu____1339]  in
    FStar_Util.mk_ref uu____1327  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1391 =
        let uu____1395 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1395
          (fun uu____1483  ->
             match uu____1483 with
             | (names1,uu____1497) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1391 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1511 ->
          (FStar_Util.incr ctr;
           (let uu____1548 =
              let uu____1550 =
                let uu____1552 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1552  in
              Prims.strcat "__" uu____1550  in
            Prims.strcat y1 uu____1548))
       in
    let top_scope =
      let uu____1602 =
        let uu____1612 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1612
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1602  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1746 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1833 =
      let uu____1835 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1835  in
    FStar_Util.format2 "%s_%s" pfx uu____1833  in
  let string_const s =
    let uu____1848 =
      let uu____1851 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1851
        (fun uu____1938  ->
           match uu____1938 with
           | (uu____1950,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1848 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1966 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1966  in
        let top_scope =
          let uu____1970 =
            let uu____1980 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1980  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1970  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____2086 =
    let uu____2087 =
      let uu____2099 = new_scope ()  in
      let uu____2109 = FStar_ST.op_Bang scopes  in uu____2099 :: uu____2109
       in
    FStar_ST.op_Colon_Equals scopes uu____2087  in
  let pop1 uu____2261 =
    let uu____2262 =
      let uu____2274 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2274
       in
    FStar_ST.op_Colon_Equals scopes uu____2262  in
  let snapshot1 uu____2431 = FStar_Common.snapshot push1 scopes ()  in
  let rollback1 depth = FStar_Common.rollback pop1 scopes depth  in
  {
    push = push1;
    pop = pop1;
    snapshot = snapshot1;
    rollback = rollback1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
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
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> fvar_lid
  
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_arity
  
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_id
  
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_token
  
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_fuel_partial_app
  
let (__proj__Mkfvar_binding__item__fvb_thunked : fvar_binding -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> fvb_thunked
  
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb  ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      let uu____2678 =
        let uu____2680 = FStar_Ident.string_of_lid fvb.fvar_lid  in
        FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2680  in
      failwith uu____2678
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____2688 =
           let uu____2690 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2690
            in
         failwith uu____2688)
      else ()
  
let binder_of_eithervar :
  'Auu____2702 'Auu____2703 .
    'Auu____2702 ->
      ('Auu____2702 * 'Auu____2703 FStar_Pervasives_Native.option)
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }
let (__proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_assumption_names
  
type env_t =
  {
  bvar_bindings:
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap
    ;
  fvar_bindings: fvar_binding FStar_Util.psmap ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string ;
  encoding_quantifier: Prims.bool }
let (__proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap)
  =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> bvar_bindings
  
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> fvar_binding FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> fvar_bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> warn
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> cache
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> current_module_name
  
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> encoding_quantifier
  
let mk_cache_entry :
  'Auu____3352 .
    'Auu____3352 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls1  ->
          let names1 =
            FStar_All.pipe_right t_decls1
              (FStar_List.collect
                 (fun uu___268_3395  ->
                    match uu___268_3395 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____3402 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls1;
            cache_symbol_assumption_names = names1
          }
  
let (use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let bvars =
      FStar_Util.psmap_fold e.bvar_bindings
        (fun _k  ->
           fun pi  ->
             fun acc  ->
               FStar_Util.pimap_fold pi
                 (fun _i  ->
                    fun uu____3462  ->
                      fun acc1  ->
                        match uu____3462 with
                        | (x,_term) ->
                            let uu____3477 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3477 :: acc1) acc) []
       in
    let allvars =
      FStar_Util.psmap_fold e.fvar_bindings
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3500 ->
          let uu____3503 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____3503
       in
    FStar_String.concat ", " (last_fvar :: bvars)
  
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      let uu____3525 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3525 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      FStar_Util.psmap_try_find env.fvar_bindings lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3593 .
    (FStar_Syntax_Syntax.bv * 'Auu____3593) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3593) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3593) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3653 =
             let uu____3660 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3660 pimap_opt  in
           FStar_Util.pimap_add uu____3653
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    fvar_binding FStar_Util.psmap -> fvar_binding FStar_Util.psmap)
  =
  fun fvb  ->
    fun fvbs  -> FStar_Util.psmap_add fvbs (fvb.fvar_lid).FStar_Ident.str fvb
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term))
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____3718 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____3718)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      let uu____3744 =
        let uu___269_3745 = env  in
        let uu____3746 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3746;
          fvar_bindings = (uu___269_3745.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___269_3745.tcenv);
          warn = (uu___269_3745.warn);
          cache = (uu___269_3745.cache);
          nolabels = (uu___269_3745.nolabels);
          use_zfuel_name = (uu___269_3745.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___269_3745.encode_non_total_function_typ);
          current_module_name = (uu___269_3745.current_module_name);
          encoding_quantifier = (uu___269_3745.encoding_quantifier)
        }  in
      (ysym, y, uu____3744)
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      let uu____3781 =
        let uu___270_3782 = env  in
        let uu____3783 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3783;
          fvar_bindings = (uu___270_3782.fvar_bindings);
          depth = (uu___270_3782.depth);
          tcenv = (uu___270_3782.tcenv);
          warn = (uu___270_3782.warn);
          cache = (uu___270_3782.cache);
          nolabels = (uu___270_3782.nolabels);
          use_zfuel_name = (uu___270_3782.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___270_3782.encode_non_total_function_typ);
          current_module_name = (uu___270_3782.current_module_name);
          encoding_quantifier = (uu___270_3782.encoding_quantifier)
        }  in
      (ysym, y, uu____3781)
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        let uu____3824 =
          let uu___271_3825 = env  in
          let uu____3826 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3826;
            fvar_bindings = (uu___271_3825.fvar_bindings);
            depth = (uu___271_3825.depth);
            tcenv = (uu___271_3825.tcenv);
            warn = (uu___271_3825.warn);
            cache = (uu___271_3825.cache);
            nolabels = (uu___271_3825.nolabels);
            use_zfuel_name = (uu___271_3825.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___271_3825.encode_non_total_function_typ);
            current_module_name = (uu___271_3825.current_module_name);
            encoding_quantifier = (uu___271_3825.encoding_quantifier)
          }  in
        (ysym, y, uu____3824)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___272_3852 = env  in
        let uu____3853 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3853;
          fvar_bindings = (uu___272_3852.fvar_bindings);
          depth = (uu___272_3852.depth);
          tcenv = (uu___272_3852.tcenv);
          warn = (uu___272_3852.warn);
          cache = (uu___272_3852.cache);
          nolabels = (uu___272_3852.nolabels);
          use_zfuel_name = (uu___272_3852.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___272_3852.encode_non_total_function_typ);
          current_module_name = (uu___272_3852.current_module_name);
          encoding_quantifier = (uu___272_3852.encoding_quantifier)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3873 = lookup_bvar_binding env a  in
      match uu____3873 with
      | FStar_Pervasives_Native.None  ->
          let uu____3884 = lookup_bvar_binding env a  in
          (match uu____3884 with
           | FStar_Pervasives_Native.None  ->
               let uu____3895 =
                 let uu____3897 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3899 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3897 uu____3899
                  in
               failwith uu____3895
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            Prims.bool -> fvar_binding)
  =
  fun lid  ->
    fun fname  ->
      fun arity  ->
        fun ftok  ->
          fun fuel_partial_app  ->
            fun thunked  ->
              let fvb =
                {
                  fvar_lid = lid;
                  smt_arity = arity;
                  smt_id = fname;
                  smt_token = ftok;
                  smt_fuel_partial_app = fuel_partial_app;
                  fvb_thunked = thunked
                }  in
              check_valid_fvb fvb; fvb
  
let (new_term_constant_and_tok_from_lid_aux :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun thunked  ->
          let fname = varops.new_fvar x  in
          let uu____3998 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.strcat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____3998 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____4062 =
                let uu___273_4063 = env  in
                let uu____4064 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___273_4063.bvar_bindings);
                  fvar_bindings = uu____4064;
                  depth = (uu___273_4063.depth);
                  tcenv = (uu___273_4063.tcenv);
                  warn = (uu___273_4063.warn);
                  cache = (uu___273_4063.cache);
                  nolabels = (uu___273_4063.nolabels);
                  use_zfuel_name = (uu___273_4063.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___273_4063.encode_non_total_function_typ);
                  current_module_name = (uu___273_4063.current_module_name);
                  encoding_quantifier = (uu___273_4063.encoding_quantifier)
                }  in
              (fname, ftok_name, uu____4062)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____4097 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____4097 with
        | (fname,ftok_name_opt,env1) ->
            let uu____4128 = FStar_Option.get ftok_name_opt  in
            (fname, uu____4128, env1)
  
let (new_term_constant_and_tok_from_lid_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun th  -> new_term_constant_and_tok_from_lid_aux env x arity th
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____4179 = lookup_fvar_binding env a  in
      match uu____4179 with
      | FStar_Pervasives_Native.None  ->
          let uu____4182 =
            let uu____4184 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4184  in
          failwith uu____4182
      | FStar_Pervasives_Native.Some s -> (check_valid_fvb s; s)
  
let (push_free_var_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            Prims.bool -> env_t)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            fun thunked  ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu___274_4231 = env  in
              let uu____4232 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___274_4231.bvar_bindings);
                fvar_bindings = uu____4232;
                depth = (uu___274_4231.depth);
                tcenv = (uu___274_4231.tcenv);
                warn = (uu___274_4231.warn);
                cache = (uu___274_4231.cache);
                nolabels = (uu___274_4231.nolabels);
                use_zfuel_name = (uu___274_4231.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___274_4231.encode_non_total_function_typ);
                current_module_name = (uu___274_4231.current_module_name);
                encoding_quantifier = (uu___274_4231.encoding_quantifier)
              }
  
let (push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            push_free_var_maybe_thunked env x arity fname ftok false
  
let (push_free_var_thunk :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            push_free_var_maybe_thunked env x arity fname ftok
              (arity = (Prims.parse_int "0"))
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____4326 =
            let uu____4334 =
              let uu____4337 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4337]  in
            (f, uu____4334)  in
          FStar_SMTEncoding_Util.mkApp uu____4326  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___275_4347 = env  in
        let uu____4348 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___275_4347.bvar_bindings);
          fvar_bindings = uu____4348;
          depth = (uu___275_4347.depth);
          tcenv = (uu___275_4347.tcenv);
          warn = (uu___275_4347.warn);
          cache = (uu___275_4347.cache);
          nolabels = (uu___275_4347.nolabels);
          use_zfuel_name = (uu___275_4347.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___275_4347.encode_non_total_function_typ);
          current_module_name = (uu___275_4347.current_module_name);
          encoding_quantifier = (uu___275_4347.encoding_quantifier)
        }
  
let (force_thunk : fvar_binding -> FStar_SMTEncoding_Term.term) =
  fun fvb  ->
    if
      (Prims.op_Negation fvb.fvb_thunked) ||
        (fvb.smt_arity <> (Prims.parse_int "0"))
    then failwith "Forcing a non-thunk in the SMT encoding"
    else ();
    FStar_SMTEncoding_Util.mkApp
      ((fvb.smt_id), [FStar_SMTEncoding_Term.dummy_value])
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4380 = lookup_fvar_binding env l  in
      match uu____4380 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          if fvb.fvb_thunked
          then
            let uu____4389 = force_thunk fvb  in
            FStar_Pervasives_Native.Some uu____4389
          else
            (match fvb.smt_fuel_partial_app with
             | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                 FStar_Pervasives_Native.Some f
             | uu____4395 ->
                 (match fvb.smt_token with
                  | FStar_Pervasives_Native.Some t ->
                      (match t.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App (uu____4403,fuel::[]) ->
                           let uu____4407 =
                             let uu____4409 =
                               let uu____4411 =
                                 FStar_SMTEncoding_Term.fv_of_term fuel  in
                               FStar_All.pipe_right uu____4411
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_Util.starts_with uu____4409 "fuel"  in
                           if uu____4407
                           then
                             let uu____4428 =
                               let uu____4429 =
                                 FStar_SMTEncoding_Util.mkFreeV
                                   ((fvb.smt_id),
                                     FStar_SMTEncoding_Term.Term_sort)
                                  in
                               FStar_SMTEncoding_Term.mk_ApplyTF uu____4429
                                 fuel
                                in
                             FStar_All.pipe_left
                               (fun _0_1  ->
                                  FStar_Pervasives_Native.Some _0_1)
                               uu____4428
                           else FStar_Pervasives_Native.Some t
                       | uu____4435 -> FStar_Pervasives_Native.Some t)
                  | uu____4436 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4454 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4454 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4458 =
            let uu____4460 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4460  in
          failwith uu____4458
  
let (lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> fvar_binding)
  = fun env  -> fun a  -> lookup_lid env a.FStar_Syntax_Syntax.v 
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      ((FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term)
        FStar_Util.either * FStar_SMTEncoding_Term.term Prims.list *
        Prims.int))
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____4522;
            FStar_SMTEncoding_Term.rng = uu____4523;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4545 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4561 =
                 let uu____4566 = force_thunk fvb  in
                 FStar_Util.Inr uu____4566  in
               (uu____4561, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4607 ->
                    ((FStar_Util.Inl
                        (FStar_SMTEncoding_Term.Var (fvb.smt_id))), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.psmap_find_map env.fvar_bindings
        (fun uu____4633  ->
           fun fvb  ->
             check_valid_fvb fvb;
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  