open Prims
let add_fuel :
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x ->
    fun tl1 ->
      let uu____19 = FStar_Options.unthrottle_inductives () in
      if uu____19 then tl1 else x :: tl1
let withenv :
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____28 ->
      ('Auu____29, 'Auu____30) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29, 'Auu____30, 'Auu____28) FStar_Pervasives_Native.tuple3
  = fun c -> fun uu____48 -> match uu____48 with | (a, b) -> (a, b, c)
let vargs :
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____59, 'Auu____60) FStar_Util.either, 'Auu____61)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____59, 'Auu____60) FStar_Util.either, 'Auu____61)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args ->
    FStar_List.filter
      (fun uu___82_107 ->
         match uu___82_107 with
         | (FStar_Util.Inl uu____116, uu____117) -> false
         | uu____122 -> true) args
let (escape : Prims.string -> Prims.string) =
  fun s -> FStar_Util.replace_char s 39 95
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid ->
    fun a ->
      let a1 =
        let uu___105_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___105_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___105_143.FStar_Syntax_Syntax.sort)
        } in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____145
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env ->
    fun lid ->
      fun i ->
        let fail1 uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____159 in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____160 with
        | (uu____165, t) ->
            let uu____167 =
              let uu____168 = FStar_Syntax_Subst.compress t in
              uu____168.FStar_Syntax_Syntax.n in
            (match uu____167 with
             | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                 let uu____189 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____189 with
                  | (binders, uu____195) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail1 ())
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid ->
    fun i ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____217
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid ->
    fun a ->
      let uu____224 =
        let uu____229 = mk_term_projector_name lid a in
        (uu____229,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____224
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid ->
    fun i ->
      let uu____236 =
        let uu____241 = mk_term_projector_name_by_pos lid i in
        (uu____241,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____236
let mk_data_tester :
  'Auu____246 .
    'Auu____246 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env ->
    fun l ->
      fun x -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit ;
  pop: Prims.unit -> Prims.unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: Prims.unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }[@@deriving show]
let (__proj__Mkvarops_t__item__push : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
let (__proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
let (__proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int)
  =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100") in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____610 =
    let uu____611 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____614 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____611, uu____614) in
  let scopes =
    let uu____634 = let uu____645 = new_scope () in [uu____645] in
    FStar_Util.mk_ref uu____634 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____686 =
        let uu____689 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____689
          (fun uu____826 ->
             match uu____826 with
             | (names1, uu____838) -> FStar_Util.smap_try_find names1 y1) in
      match uu____686 with
      | FStar_Pervasives_Native.None -> y1
      | FStar_Pervasives_Native.Some uu____847 ->
          (FStar_Util.incr ctr;
           (let uu____954 =
              let uu____955 =
                let uu____956 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____956 in
              Prims.strcat "__" uu____955 in
            Prims.strcat y1 uu____954)) in
    let top_scope =
      let uu____1055 =
        let uu____1064 = FStar_ST.op_Bang scopes in FStar_List.hd uu____1064 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1055 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1227 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1433 =
      let uu____1434 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1434 in
    FStar_Util.format2 "%s_%s" pfx uu____1433 in
  let string_const s =
    let uu____1439 =
      let uu____1442 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1442
        (fun uu____1579 ->
           match uu____1579 with
           | (uu____1590, strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1439 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let id1 = next_id1 () in
        let f =
          let uu____1603 = FStar_SMTEncoding_Util.mk_String_const id1 in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1603 in
        let top_scope =
          let uu____1607 =
            let uu____1616 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1616 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1607 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1768 =
    let uu____1769 =
      let uu____1780 = new_scope () in
      let uu____1789 = FStar_ST.op_Bang scopes in uu____1780 :: uu____1789 in
    FStar_ST.op_Colon_Equals scopes uu____1769 in
  let pop1 uu____2041 =
    let uu____2042 =
      let uu____2053 = FStar_ST.op_Bang scopes in FStar_List.tl uu____2053 in
    FStar_ST.op_Colon_Equals scopes uu____2042 in
  {
    push = push1;
    pop = pop1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let (unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv) =
  fun x ->
    let uu___106_2305 = x in
    let uu____2306 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____2306;
      FStar_Syntax_Syntax.index = (uu___106_2305.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___106_2305.FStar_Syntax_Syntax.sort)
    }
type fvar_binding =
  {
  fvar_lid: FStar_Ident.lident ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option }[@@deriving
                                                                  show]
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__fvar_lid
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_arity
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_id
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_token
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_fuel_partial_app
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of fvar_binding [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_var _0 -> true | uu____2419 -> false
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Binding_var _0 -> _0
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_fvar _0 -> true | uu____2443 -> false
let (__proj__Binding_fvar__item___0 : binding -> fvar_binding) =
  fun projectee -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar :
  'Auu____2454 'Auu____2455 .
    'Auu____2454 ->
      ('Auu____2454, 'Auu____2455 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1 -> (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
let (__proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string) =
  fun projectee ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
type env_t =
  {
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }[@@deriving show]
let (__proj__Mkenv_t__item__bindings : env_t -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__bindings
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
let mk_cache_entry :
  'Auu____2751 .
    'Auu____2751 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env ->
    fun tsym ->
      fun cvar_sorts ->
        fun t_decls1 ->
          let names1 =
            FStar_All.pipe_right t_decls1
              (FStar_List.collect
                 (fun uu___83_2785 ->
                    match uu___83_2785 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2789 -> [])) in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls1;
            cache_symbol_assumption_names = names1
          }
let (use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun ce ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let (print_env : env_t -> Prims.string) =
  fun e ->
    let uu____2798 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___84_2808 ->
              match uu___84_2808 with
              | Binding_var (x, uu____2810) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid)) in
    FStar_All.pipe_right uu____2798 (FStar_String.concat ", ")
let lookup_binding :
  'Auu____2817 .
    env_t ->
      (binding -> 'Auu____2817 FStar_Pervasives_Native.option) ->
        'Auu____2817 FStar_Pervasives_Native.option
  = fun env -> fun f -> FStar_Util.find_map env.bindings f
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu____2845 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2845
      then
        let uu____2848 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2848
      else FStar_Pervasives_Native.None
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    fun s ->
      let xsym = varops.fresh x in
      let uu____2861 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2861)
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string, FStar_SMTEncoding_Term.term, env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun x ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___107_2877 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___107_2877.tcenv);
           warn = (uu___107_2877.warn);
           cache = (uu___107_2877.cache);
           nolabels = (uu___107_2877.nolabels);
           use_zfuel_name = (uu___107_2877.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___107_2877.encode_non_total_function_typ);
           current_module_name = (uu___107_2877.current_module_name)
         }))
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string, FStar_SMTEncoding_Term.term, env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun x ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___108_2895 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___108_2895.depth);
           tcenv = (uu___108_2895.tcenv);
           warn = (uu___108_2895.warn);
           cache = (uu___108_2895.cache);
           nolabels = (uu___108_2895.nolabels);
           use_zfuel_name = (uu___108_2895.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___108_2895.encode_non_total_function_typ);
           current_module_name = (uu___108_2895.current_module_name)
         }))
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string, FStar_SMTEncoding_Term.term, env_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun x ->
      fun str ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___109_2916 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___109_2916.depth);
             tcenv = (uu___109_2916.tcenv);
             warn = (uu___109_2916.warn);
             cache = (uu___109_2916.cache);
             nolabels = (uu___109_2916.nolabels);
             use_zfuel_name = (uu___109_2916.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___109_2916.encode_non_total_function_typ);
             current_module_name = (uu___109_2916.current_module_name)
           }))
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env ->
    fun x ->
      fun t ->
        let uu___110_2926 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___110_2926.depth);
          tcenv = (uu___110_2926.tcenv);
          warn = (uu___110_2926.warn);
          cache = (uu___110_2926.cache);
          nolabels = (uu___110_2926.nolabels);
          use_zfuel_name = (uu___110_2926.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___110_2926.encode_non_total_function_typ);
          current_module_name = (uu___110_2926.current_module_name)
        }
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env ->
    fun a ->
      let aux a' =
        lookup_binding env
          (fun uu___85_2950 ->
             match uu___85_2950 with
             | Binding_var (b, t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2963 -> FStar_Pervasives_Native.None) in
      let uu____2968 = aux a in
      match uu____2968 with
      | FStar_Pervasives_Native.None ->
          let a2 = unmangle a in
          let uu____2980 = aux a2 in
          (match uu____2980 with
           | FStar_Pervasives_Native.None ->
               let uu____2991 =
                 let uu____2992 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2993 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2992 uu____2993 in
               failwith uu____2991
           | FStar_Pervasives_Native.Some (b, t) -> t)
      | FStar_Pervasives_Native.Some (b, t) -> t
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            fvar_binding)
  =
  fun lid ->
    fun fname ->
      fun arity ->
        fun ftok ->
          fun fuel_partial_app ->
            {
              fvar_lid = lid;
              smt_arity = arity;
              smt_id = fname;
              smt_token = ftok;
              smt_fuel_partial_app = fuel_partial_app
            }
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        (Prims.string, Prims.string, env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun x ->
      fun arity ->
        let fname = varops.new_fvar x in
        let ftok_name = Prims.strcat fname "@tok" in
        let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, []) in
        let fvb =
          mk_fvb x fname arity (FStar_Pervasives_Native.Some ftok)
            FStar_Pervasives_Native.None in
        (fname, ftok_name,
          (let uu___111_3051 = env in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___111_3051.depth);
             tcenv = (uu___111_3051.tcenv);
             warn = (uu___111_3051.warn);
             cache = (uu___111_3051.cache);
             nolabels = (uu___111_3051.nolabels);
             use_zfuel_name = (uu___111_3051.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___111_3051.encode_non_total_function_typ);
             current_module_name = (uu___111_3051.current_module_name)
           }))
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env ->
    fun a ->
      lookup_binding env
        (fun uu___86_3062 ->
           match uu___86_3062 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____3066 -> FStar_Pervasives_Native.None)
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env ->
    fun s ->
      let uu____3073 =
        lookup_binding env
          (fun uu___87_3078 ->
             match uu___87_3078 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____3082 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____3073 FStar_Option.isSome
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env ->
    fun a ->
      let uu____3091 = try_lookup_lid env a in
      match uu____3091 with
      | FStar_Pervasives_Native.None ->
          let uu____3094 =
            let uu____3095 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____3095 in
          failwith uu____3094
      | FStar_Pervasives_Native.Some s -> s
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
            let fvb = mk_fvb x fname arity ftok FStar_Pervasives_Native.None in
            let uu___112_3117 = env in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___112_3117.depth);
              tcenv = (uu___112_3117.tcenv);
              warn = (uu___112_3117.warn);
              cache = (uu___112_3117.cache);
              nolabels = (uu___112_3117.nolabels);
              use_zfuel_name = (uu___112_3117.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___112_3117.encode_non_total_function_typ);
              current_module_name = (uu___112_3117.current_module_name)
            }
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env ->
    fun x ->
      fun f ->
        let fvb = lookup_lid env x in
        let t3 =
          let uu____3129 =
            let uu____3136 =
              let uu____3139 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
              [uu____3139] in
            (f, uu____3136) in
          FStar_SMTEncoding_Util.mkApp uu____3129 in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) in
        let uu___113_3145 = env in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___113_3145.depth);
          tcenv = (uu___113_3145.tcenv);
          warn = (uu___113_3145.warn);
          cache = (uu___113_3145.cache);
          nolabels = (uu___113_3145.nolabels);
          use_zfuel_name = (uu___113_3145.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___113_3145.encode_non_total_function_typ);
          current_module_name = (uu___113_3145.current_module_name)
        }
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____3154 = try_lookup_lid env l in
      match uu____3154 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3163 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3171, fuel::[]) ->
                         let uu____3175 =
                           let uu____3176 =
                             let uu____3177 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____3177
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____3176 "fuel" in
                         if uu____3175
                         then
                           let uu____3180 =
                             let uu____3181 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3181
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_40 -> FStar_Pervasives_Native.Some _0_40)
                             uu____3180
                         else FStar_Pervasives_Native.Some t
                     | uu____3185 -> FStar_Pervasives_Native.Some t)
                | uu____3186 -> FStar_Pervasives_Native.None))
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env ->
    fun a ->
      let uu____3199 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____3199 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let uu____3203 =
            let uu____3204 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3204 in
          failwith uu____3203
let (lookup_free_var_name :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string, Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun a ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v in
      ((fvb.smt_id), (fvb.smt_arity))
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term Prims.list,
        Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun a ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf);
            FStar_SMTEncoding_Term.freevars = uu____3249;
            FStar_SMTEncoding_Term.rng = uu____3250;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____3265 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g, fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____3293 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun nm ->
      FStar_Util.find_map env.bindings
        (fun uu___88_3306 ->
           match uu___88_3306 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____3310 -> FStar_Pervasives_Native.None)
let mkForall_fuel' :
  'Auu____3314 .
    'Auu____3314 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,
        FStar_SMTEncoding_Term.fvs, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple3 -> FStar_SMTEncoding_Term.term
  =
  fun n1 ->
    fun uu____3332 ->
      match uu____3332 with
      | (pats, vars, body) ->
          let fallback uu____3357 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3362 = FStar_Options.unthrottle_inductives () in
          if uu____3362
          then fallback ()
          else
            (let uu____3364 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3364 with
             | (fsym, fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType", args)
                               ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____3395 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And, guards) ->
                             let uu____3416 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3416
                         | uu____3419 ->
                             let uu____3420 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3420 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3425 -> body in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,
    FStar_SMTEncoding_Term.fvs, FStar_SMTEncoding_Term.term)
    FStar_Pervasives_Native.tuple3 -> FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1")
let (head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3466 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3479 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3486 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3487 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3504 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3521 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3523 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3523 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3541;
             FStar_Syntax_Syntax.vars = uu____3542;_},
           uu____3543)
          ->
          let uu____3564 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3564 FStar_Option.isNone
      | uu____3581 -> false
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____3588 =
        let uu____3589 = FStar_Syntax_Util.un_uinst t in
        uu____3589.FStar_Syntax_Syntax.n in
      match uu____3588 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3592, uu____3593, FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___89_3614 ->
                  match uu___89_3614 with
                  | FStar_Syntax_Syntax.TOTAL -> true
                  | uu____3615 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3617 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3617 FStar_Option.isSome
      | uu____3634 -> false
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun t ->
      let uu____3641 = head_normal env t in
      if uu____3641
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let (norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun t ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____3652 =
      let uu____3653 = FStar_Syntax_Syntax.null_binder t in [uu____3653] in
    let uu____3654 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3652 uu____3654 FStar_Pervasives_Native.None
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string, FStar_SMTEncoding_Term.sort)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_SMTEncoding_Term.term)
  =
  fun e ->
    fun vars ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out ->
              fun var ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort ->
                    let uu____3692 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3692
                | s ->
                    let uu____3703 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3703) e)
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e ->
    fun args ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let raise_arity_mismatch :
  'Auu____3721 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3721
  =
  fun head1 ->
    fun arity ->
      fun n_args ->
        fun rng ->
          let uu____3738 =
            let uu____3743 =
              let uu____3744 = FStar_Util.string_of_int arity in
              let uu____3745 = FStar_Util.string_of_int n_args in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3744 uu____3745 in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3743) in
          FStar_Errors.raise_error uu____3738 rng
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun head1 ->
      fun arity ->
        fun args ->
          let n_args = FStar_List.length args in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____3776 = FStar_Util.first_N arity args in
               match uu____3776 with
               | (args1, rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1) in
                   mk_Apply_args head2 rest)
            else
              (let uu____3799 = FStar_SMTEncoding_Term.op_to_string head1 in
               raise_arity_mismatch uu____3799 arity n_args rng)
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___90_3806 ->
    match uu___90_3806 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3807 -> false
let (is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun vars ->
      fun body ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,
              f::{
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV y;
                   FStar_SMTEncoding_Term.freevars = uu____3843;
                   FStar_SMTEncoding_Term.rng = uu____3844;_}::[]),
             x::xs1) when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)
              -> check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f, args),
             uu____3867) ->
              let uu____3876 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a ->
                        fun v1 ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3887 -> false) args (FStar_List.rev xs)) in
              if uu____3876
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3891, []) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3895 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv ->
                        let uu____3899 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3899)) in
              if uu____3895
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3903 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv, Prims.string, FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Let_rec_unencodeable -> true | uu____4125 -> false
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Inner_let_rec -> true | uu____4129 -> false
let (as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t0 ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____4148 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4161 ->
            let uu____4168 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4168
        | uu____4169 ->
            if norm1
            then let uu____4170 = whnf env t1 in aux false uu____4170
            else
              (let uu____4172 =
                 let uu____4173 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4174 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4173 uu____4174 in
               failwith uu____4172) in
      aux true t0
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv, uu____4206) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4211 ->
        let uu____4212 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4212)
let is_arithmetic_primitive :
  'Auu____4226 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4226 Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____4246::uu____4247::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____4251::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4254 -> false
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> true
    | uu____4275 -> false
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> FStar_Util.int_of_string n1
    | uu____4290 -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'Auu____4294 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, 'Auu____4294)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____4333)::uu____4334::uu____4335::[]) ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____4386)::uu____4387::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4424 -> false
let rec (encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c ->
    fun env ->
      match c with
      | FStar_Const.Const_unit -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true) ->
          let uu____4643 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4643, [])
      | FStar_Const.Const_bool (false) ->
          let uu____4646 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4646, [])
      | FStar_Const.Const_char c1 ->
          let uu____4650 =
            let uu____4651 =
              let uu____4658 =
                let uu____4661 =
                  let uu____4662 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4662 in
                [uu____4661] in
              ("FStar.Char.__char_of_int", uu____4658) in
            FStar_SMTEncoding_Util.mkApp uu____4651 in
          (uu____4650, [])
      | FStar_Const.Const_int (i, FStar_Pervasives_Native.None) ->
          let uu____4678 =
            let uu____4679 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4679 in
          (uu____4678, [])
      | FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s, uu____4700) ->
          let uu____4701 = varops.string_const s in (uu____4701, [])
      | FStar_Const.Const_range uu____4704 ->
          let uu____4705 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4705, [])
      | FStar_Const.Const_effect -> (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4711 =
            let uu____4712 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4712 in
          failwith uu____4711
and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,
          FStar_SMTEncoding_Term.term Prims.list, env_t,
          FStar_SMTEncoding_Term.decls_t, FStar_Syntax_Syntax.bv Prims.list)
          FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt ->
    fun bs ->
      fun env ->
        (let uu____4741 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4741
         then
           let uu____4742 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4742
         else ());
        (let uu____4744 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4828 ->
                   fun b ->
                     match uu____4828 with
                     | (vars, guards, env1, decls, names1) ->
                         let uu____4907 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4923 = gen_term_var env1 x in
                           match uu____4923 with
                           | (xxsym, xx, env') ->
                               let uu____4947 =
                                 let uu____4952 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4952 env1 xx in
                               (match uu____4947 with
                                | (guard_x_t, decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4907 with
                          | (v1, g, env2, decls', n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4744 with
         | (vars, guards, env1, decls, names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu____5111 = encode_term t env in
          match uu____5111 with
          | (t1, decls) ->
              let uu____5122 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____5122, decls)
and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu____5133 = encode_term t env in
          match uu____5133 with
          | (t1, decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None ->
                   let uu____5148 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____5148, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5150 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____5150, decls))
and (encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun head1 ->
      fun args_e ->
        let uu____5156 = encode_args args_e env in
        match uu____5156 with
        | (arg_tms, decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5175 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5184 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5184 in
            let binary arg_tms1 =
              let uu____5197 =
                let uu____5198 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5198 in
              let uu____5199 =
                let uu____5200 =
                  let uu____5201 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5201 in
                FStar_SMTEncoding_Term.unboxInt uu____5200 in
              (uu____5197, uu____5199) in
            let mk_default uu____5207 =
              let uu____5208 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5208 with
              | (fname, fuel_args, arity) ->
                  let args = FStar_List.append fuel_args arg_tms in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args in
            let mk_l a op mk_args ts =
              let uu____5258 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5258
              then
                let uu____5259 = let uu____5260 = mk_args ts in op uu____5260 in
                FStar_All.pipe_right uu____5259 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5289 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5289
              then
                let uu____5290 = binary ts in
                match uu____5290 with
                | (t1, t2) ->
                    let uu____5297 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5297
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5301 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5301
                 then
                   let uu____5302 = op (binary ts) in
                   FStar_All.pipe_right uu____5302
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 =
              mk_l ()
                (fun a415 -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a415)
                (fun a416 -> (Obj.magic binary) a416) in
            let sub1 =
              mk_l ()
                (fun a417 -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a417)
                (fun a418 -> (Obj.magic binary) a418) in
            let minus =
              mk_l ()
                (fun a419 -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a419)
                (fun a420 -> (Obj.magic unary) a420) in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____5425 =
              let uu____5434 =
                FStar_List.tryFind
                  (fun uu____5456 ->
                     match uu____5456 with
                     | (l, uu____5466) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5434 FStar_Util.must in
            (match uu____5425 with
             | (uu____5505, op) ->
                 let uu____5515 = op arg_tms in (uu____5515, decls))
and (encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun head1 ->
      fun args_e ->
        let uu____5523 = FStar_List.hd args_e in
        match uu____5523 with
        | (tm_sz, uu____5531) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5541 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5541 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5549 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5549);
                   t_decls1) in
            let uu____5550 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____5570::(sz_arg, uu____5572)::uu____5573::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5622 =
                    let uu____5625 = FStar_List.tail args_e in
                    FStar_List.tail uu____5625 in
                  let uu____5628 =
                    let uu____5631 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5631 in
                  (uu____5622, uu____5628)
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____5637::(sz_arg, uu____5639)::uu____5640::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5689 =
                    let uu____5690 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5690 in
                  failwith uu____5689
              | uu____5699 ->
                  let uu____5706 = FStar_List.tail args_e in
                  (uu____5706, FStar_Pervasives_Native.None) in
            (match uu____5550 with
             | (arg_tms, ext_sz) ->
                 let uu____5729 = encode_args arg_tms env in
                 (match uu____5729 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5750 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5759 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5759 in
                      let unary_arith arg_tms2 =
                        let uu____5768 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5768 in
                      let binary arg_tms2 =
                        let uu____5781 =
                          let uu____5782 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5782 in
                        let uu____5783 =
                          let uu____5784 =
                            let uu____5785 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5785 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5784 in
                        (uu____5781, uu____5783) in
                      let binary_arith arg_tms2 =
                        let uu____5800 =
                          let uu____5801 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5801 in
                        let uu____5802 =
                          let uu____5803 =
                            let uu____5804 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5804 in
                          FStar_SMTEncoding_Term.unboxInt uu____5803 in
                        (uu____5800, uu____5802) in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5846 =
                          let uu____5847 = mk_args ts in op uu____5847 in
                        FStar_All.pipe_right uu____5846 resBox in
                      let bv_and =
                        mk_bv ()
                          (fun a421 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a421)
                          (fun a422 -> (Obj.magic binary) a422)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv ()
                          (fun a423 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a423)
                          (fun a424 -> (Obj.magic binary) a424)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv ()
                          (fun a425 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a425)
                          (fun a426 -> (Obj.magic binary) a426)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv ()
                          (fun a427 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a427)
                          (fun a428 -> (Obj.magic binary) a428)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv ()
                          (fun a429 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a429)
                          (fun a430 -> (Obj.magic binary) a430)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv ()
                          (fun a431 ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a431)
                          (fun a432 -> (Obj.magic binary_arith) a432)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv ()
                          (fun a433 ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a433)
                          (fun a434 -> (Obj.magic binary_arith) a434)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv ()
                          (fun a435 ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a435)
                          (fun a436 -> (Obj.magic binary_arith) a436)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv ()
                          (fun a437 ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a437)
                          (fun a438 -> (Obj.magic binary_arith) a438)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv ()
                          (fun a439 ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a439)
                          (fun a440 -> (Obj.magic binary_arith) a440)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv ()
                          (fun a441 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a441)
                          (fun a442 -> (Obj.magic binary) a442)
                          FStar_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu____5911 =
                          let uu____5914 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5914 in
                        let uu____5916 =
                          let uu____5919 =
                            let uu____5920 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu____5920 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5919 in
                        mk_bv () (fun a443 -> (Obj.magic uu____5911) a443)
                          (fun a444 -> (Obj.magic unary) a444) uu____5916
                          arg_tms2 in
                      let to_int1 =
                        mk_bv ()
                          (fun a445 ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a445) (fun a446 -> (Obj.magic unary) a446)
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv ()
                          (fun a447 ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a447)
                          (fun a448 -> (Obj.magic unary_arith) a448)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____6119 =
                        let uu____6128 =
                          FStar_List.tryFind
                            (fun uu____6150 ->
                               match uu____6150 with
                               | (l, uu____6160) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6128 FStar_Util.must in
                      (match uu____6119 with
                       | (uu____6201, op) ->
                           let uu____6211 = op arg_tms1 in
                           (uu____6211, (FStar_List.append sz_decls decls)))))
and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    fun env ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6222 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6222
       then
         let uu____6223 = FStar_Syntax_Print.tag_of_term t in
         let uu____6224 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6225 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6223 uu____6224
           uu____6225
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6231 ->
           let uu____6256 =
             let uu____6257 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6258 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6259 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6260 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6257
               uu____6258 uu____6259 uu____6260 in
           failwith uu____6256
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____6265 =
             let uu____6266 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6267 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6268 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6269 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6266
               uu____6267 uu____6268 uu____6269 in
           failwith uu____6265
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6275 = FStar_Syntax_Util.unfold_lazy i in
           encode_term uu____6275 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6277 =
             let uu____6278 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6278 in
           failwith uu____6277
       | FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____6285), uu____6286) ->
           let uu____6335 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____6343 -> false in
           if uu____6335
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt, uu____6360) ->
           let tv =
             let uu____6366 = FStar_Reflection_Basic.inspect_ln qt in
             FStar_Reflection_Embeddings.embed_term_view
               t.FStar_Syntax_Syntax.pos uu____6366 in
           let t1 =
             let uu____6370 =
               let uu____6379 = FStar_Syntax_Syntax.as_arg tv in [uu____6379] in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____6370 in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____6381) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6391 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6391, [])
       | FStar_Syntax_Syntax.Tm_type uu____6394 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____6398) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
           let module_name = env.current_module_name in
           let uu____6423 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6423 with
            | (binders1, res) ->
                let uu____6434 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6434
                then
                  let uu____6439 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6439 with
                   | (vars, guards, env', decls, uu____6464) ->
                       let fsym =
                         let uu____6482 = varops.fresh "f" in
                         (uu____6482, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6485 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___114_6494 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___114_6494.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___114_6494.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___114_6494.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___114_6494.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___114_6494.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___114_6494.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___114_6494.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___114_6494.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___114_6494.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___114_6494.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___114_6494.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___114_6494.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___114_6494.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___114_6494.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___114_6494.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___114_6494.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___114_6494.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___114_6494.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___114_6494.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___114_6494.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___114_6494.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___114_6494.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___114_6494.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___114_6494.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___114_6494.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___114_6494.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___114_6494.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___114_6494.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___114_6494.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___114_6494.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___114_6494.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___114_6494.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___114_6494.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___114_6494.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___114_6494.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6485 with
                        | (pre_opt, res_t) ->
                            let uu____6505 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6505 with
                             | (res_pred, decls') ->
                                 let uu____6516 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None ->
                                       let uu____6529 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6529, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6533 =
                                         encode_formula pre env' in
                                       (match uu____6533 with
                                        | (guard, decls0) ->
                                            let uu____6546 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6546, decls0)) in
                                 (match uu____6516 with
                                  | (guards1, guard_decls) ->
                                      let t_interp =
                                        let uu____6558 =
                                          let uu____6569 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6569) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6558 in
                                      let cvars =
                                        let uu____6587 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6587
                                          (FStar_List.filter
                                             (fun uu____6601 ->
                                                match uu____6601 with
                                                | (x, uu____6607) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6626 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6626 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6634 =
                                             let uu____6635 =
                                               let uu____6642 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6642) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6635 in
                                           (uu____6634,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None ->
                                           let tsym =
                                             let uu____6662 =
                                               let uu____6663 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6663 in
                                             varops.mk_unique uu____6662 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6674 =
                                               FStar_Options.log_queries () in
                                             if uu____6674
                                             then
                                               let uu____6677 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6677
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6685 =
                                               let uu____6692 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6692) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6685 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6704 =
                                               let uu____6711 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6711,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6704 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____6732 =
                                               let uu____6739 =
                                                 let uu____6740 =
                                                   let uu____6751 =
                                                     let uu____6752 =
                                                       let uu____6757 =
                                                         let uu____6758 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6758 in
                                                       (f_has_t, uu____6757) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6752 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6751) in
                                                 mkForall_fuel uu____6740 in
                                               (uu____6739,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6732 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6781 =
                                               let uu____6788 =
                                                 let uu____6789 =
                                                   let uu____6800 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6800) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6789 in
                                               (uu____6788,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6781 in
                                           let t_decls1 =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6825 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1 in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6825);
                                            (t1, t_decls1)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____6840 =
                       let uu____6847 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6847,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6840 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6859 =
                       let uu____6866 =
                         let uu____6867 =
                           let uu____6878 =
                             let uu____6879 =
                               let uu____6884 =
                                 let uu____6885 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6885 in
                               (f_has_t, uu____6884) in
                             FStar_SMTEncoding_Util.mkImp uu____6879 in
                           ([[f_has_t]], [fsym], uu____6878) in
                         mkForall_fuel uu____6867 in
                       (uu____6866, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6859 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6912 ->
           let uu____6919 =
             let uu____6924 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6924 with
             | {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f);
                 FStar_Syntax_Syntax.pos = uu____6931;
                 FStar_Syntax_Syntax.vars = uu____6932;_} ->
                 let uu____6939 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6939 with
                  | (b, f1) ->
                      let uu____6964 =
                        let uu____6965 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6965 in
                      (uu____6964, f1))
             | uu____6974 -> failwith "impossible" in
           (match uu____6919 with
            | (x, f) ->
                let uu____6985 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6985 with
                 | (base_t, decls) ->
                     let uu____6996 = gen_term_var env x in
                     (match uu____6996 with
                      | (x1, xtm, env') ->
                          let uu____7010 = encode_formula f env' in
                          (match uu____7010 with
                           | (refinement, decls') ->
                               let uu____7021 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____7021 with
                                | (fsym, fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____7037 =
                                        let uu____7040 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____7047 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____7040
                                          uu____7047 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7037 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7080 ->
                                              match uu____7080 with
                                              | (y, uu____7086) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____7119 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7119 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7127 =
                                           let uu____7128 =
                                             let uu____7135 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7135) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7128 in
                                         (uu____7127,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7156 =
                                             let uu____7157 =
                                               let uu____7158 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7158 in
                                             Prims.strcat module_name
                                               uu____7157 in
                                           varops.mk_unique uu____7156 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____7172 =
                                             let uu____7179 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7179) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7172 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____7196 =
                                             try_lookup_lid env
                                               FStar_Parser_Const.haseq_lid in
                                           match uu____7196 with
                                           | FStar_Pervasives_Native.None ->
                                               []
                                           | FStar_Pervasives_Native.Some
                                               uu____7201 ->
                                               let uu____7202 =
                                                 let uu____7203 =
                                                   let uu____7210 =
                                                     let uu____7211 =
                                                       let uu____7222 =
                                                         FStar_SMTEncoding_Util.mkIff
                                                           (t_haseq_ref,
                                                             t_haseq_base) in
                                                       ([[t_haseq_ref]],
                                                         cvars1, uu____7222) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____7211 in
                                                   (uu____7210,
                                                     (FStar_Pervasives_Native.Some
                                                        (Prims.strcat
                                                           "haseq for " tsym)),
                                                     (Prims.strcat "haseq"
                                                        tsym)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7203 in
                                               [uu____7202] in
                                         let t_kinding =
                                           let uu____7240 =
                                             let uu____7247 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7247,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7240 in
                                         let t_interp =
                                           let uu____7265 =
                                             let uu____7272 =
                                               let uu____7273 =
                                                 let uu____7284 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7284) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7273 in
                                             let uu____7307 =
                                               let uu____7310 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7310 in
                                             (uu____7272, uu____7307,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7265 in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                (FStar_List.append
                                                   [tdecl;
                                                   t_kinding;
                                                   t_interp] t_haseq1)) in
                                         ((let uu____7317 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1 in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7317);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv, k) ->
           let ttm =
             let uu____7347 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7347 in
           let uu____7348 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7348 with
            | (t_has_k, decls) ->
                let d =
                  let uu____7360 =
                    let uu____7367 =
                      let uu____7368 =
                        let uu____7369 =
                          let uu____7370 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7370 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7369 in
                      varops.mk_unique uu____7368 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7367) in
                  FStar_SMTEncoding_Util.mkAssume uu____7360 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7375 ->
           let uu____7390 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7390 with
            | (head1, args_e) ->
                let uu____7431 =
                  let uu____7444 =
                    let uu____7445 = FStar_Syntax_Subst.compress head1 in
                    uu____7445.FStar_Syntax_Syntax.n in
                  (uu____7444, args_e) in
                (match uu____7431 with
                 | uu____7460 when head_redex env head1 ->
                     let uu____7473 = whnf env t in
                     encode_term uu____7473 env
                 | uu____7474 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7493 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7507;
                       FStar_Syntax_Syntax.vars = uu____7508;_},
                     uu____7509),
                    uu____7510::(v1, uu____7512)::(v2, uu____7514)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7565 = encode_term v1 env in
                     (match uu____7565 with
                      | (v11, decls1) ->
                          let uu____7576 = encode_term v2 env in
                          (match uu____7576 with
                           | (v21, decls2) ->
                               let uu____7587 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7587,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar fv,
                    uu____7591::(v1, uu____7593)::(v2, uu____7595)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7642 = encode_term v1 env in
                     (match uu____7642 with
                      | (v11, decls1) ->
                          let uu____7653 = encode_term v2 env in
                          (match uu____7653 with
                           | (v21, decls2) ->
                               let uu____7664 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7664,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of), (arg, uu____7668)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of),
                    (arg, uu____7694)::(rng, uu____7696)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify), uu____7731) ->
                     let e0 =
                       let uu____7749 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7749 in
                     ((let uu____7757 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7757
                       then
                         let uu____7758 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7758
                       else ());
                      (let e =
                         let uu____7763 =
                           let uu____7764 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7765 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7764
                             uu____7765 in
                         uu____7763 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____7774),
                    (arg, uu____7776)::[]) -> encode_term arg env
                 | uu____7801 ->
                     let uu____7814 = encode_args args_e env in
                     (match uu____7814 with
                      | (args, decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7869 = encode_term head1 env in
                            match uu____7869 with
                            | (head2, decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals, c)
                                     ->
                                     let uu____7933 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7933 with
                                      | (formals1, rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8011 ->
                                                 fun uu____8012 ->
                                                   match (uu____8011,
                                                           uu____8012)
                                                   with
                                                   | ((bv, uu____8034),
                                                      (a, uu____8036)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____8054 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____8054
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____8059 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____8059 with
                                           | (has_type, decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____8074 =
                                                   let uu____8081 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____8090 =
                                                     let uu____8091 =
                                                       let uu____8092 =
                                                         let uu____8093 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____8093 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8092 in
                                                     varops.mk_unique
                                                       uu____8091 in
                                                   (uu____8081,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8090) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8074 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____8110 = lookup_free_var_sym env fv in
                            match uu____8110 with
                            | (fname, fuel_args, arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____8142;
                                   FStar_Syntax_Syntax.vars = uu____8143;_},
                                 uu____8144)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____8155;
                                   FStar_Syntax_Syntax.vars = uu____8156;_},
                                 uu____8157)
                                ->
                                let uu____8162 =
                                  let uu____8163 =
                                    let uu____8168 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8168
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8163
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8162
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8198 =
                                  let uu____8199 =
                                    let uu____8204 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8204
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8199
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8198
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8233, (FStar_Util.Inl t1, uu____8235),
                                 uu____8236)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8285, (FStar_Util.Inr c, uu____8287),
                                 uu____8288)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8337 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8364 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8364 in
                               let uu____8365 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8365 with
                                | (formals, c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8381;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8382;_},
                                          uu____8383)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____8397 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
           let uu____8446 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8446 with
            | (bs1, body1, opening) ->
                let fallback uu____8469 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8476 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8476, [decl]) in
                let is_impure rc =
                  let uu____8483 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8483 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None ->
                        let uu____8493 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8493
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8513 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8513
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8517 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8517)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None ->
                     ((let uu____8524 =
                         let uu____8529 =
                           let uu____8530 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8530 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8529) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8524);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8532 =
                       (is_impure rc) &&
                         (let uu____8534 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8534) in
                     if uu____8532
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8541 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8541 with
                        | (vars, guards, envbody, decls, uu____8566) ->
                            let body2 =
                              let uu____8580 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8580
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8582 = encode_term body2 envbody in
                            (match uu____8582 with
                             | (body3, decls') ->
                                 let uu____8593 =
                                   let uu____8602 = codomain_eff rc in
                                   match uu____8602 with
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8621 = encode_term tfun env in
                                       (match uu____8621 with
                                        | (t1, decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8593 with
                                  | (arrow_t_opt, decls'') ->
                                      let key_body =
                                        let uu____8653 =
                                          let uu____8664 =
                                            let uu____8665 =
                                              let uu____8670 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8670, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8665 in
                                          ([], vars, uu____8664) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8653 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8682 =
                                              let uu____8685 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8685
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8682 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8704 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8704 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8712 =
                                             let uu____8713 =
                                               let uu____8720 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8720) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8713 in
                                           (uu____8712,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None ->
                                           let uu____8731 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8731 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8742 =
                                                    let uu____8743 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8743 = cache_size in
                                                  if uu____8742
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'') in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1 in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____8759 =
                                                      let uu____8760 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8760 in
                                                    varops.mk_unique
                                                      uu____8759 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8767 =
                                                    let uu____8774 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8774) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8767 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                      -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1 in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym in
                                                      let uu____8792 =
                                                        let uu____8793 =
                                                          let uu____8800 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8800,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8793 in
                                                      [uu____8792] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8813 =
                                                    let uu____8820 =
                                                      let uu____8821 =
                                                        let uu____8832 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8832) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8821 in
                                                    (uu____8820,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8813 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8849 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8849);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8852,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8853;
               FStar_Syntax_Syntax.lbunivs = uu____8854;
               FStar_Syntax_Syntax.lbtyp = uu____8855;
               FStar_Syntax_Syntax.lbeff = uu____8856;
               FStar_Syntax_Syntax.lbdef = uu____8857;
               FStar_Syntax_Syntax.lbattrs = uu____8858;
               FStar_Syntax_Syntax.lbpos = uu____8859;_}::uu____8860),
            uu____8861)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu____8891;
               FStar_Syntax_Syntax.lbtyp = t1;
               FStar_Syntax_Syntax.lbeff = uu____8893;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu____8895;
               FStar_Syntax_Syntax.lbpos = uu____8896;_}::[]),
            e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8920 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e, pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and (encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term,
                   FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    fun t1 ->
      fun e1 ->
        fun e2 ->
          fun env ->
            fun encode_body ->
              let uu____8990 =
                let uu____8995 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu____8995 env in
              match uu____8990 with
              | (ee1, decls1) ->
                  let uu____9016 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9016 with
                   | (xs, e21) ->
                       let uu____9041 = FStar_List.hd xs in
                       (match uu____9041 with
                        | (x1, uu____9055) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____9057 = encode_body e21 env' in
                            (match uu____9057 with
                             | (ee2, decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    fun pats ->
      fun default_case ->
        fun env ->
          fun encode_br ->
            let uu____9089 =
              let uu____9096 =
                let uu____9097 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9097 in
              gen_term_var env uu____9096 in
            match uu____9089 with
            | (scrsym, scr', env1) ->
                let uu____9105 = encode_term e env1 in
                (match uu____9105 with
                 | (scr, decls) ->
                     let uu____9116 =
                       let encode_branch b uu____9141 =
                         match uu____9141 with
                         | (else_case, decls1) ->
                             let uu____9160 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9160 with
                              | (p, w, br) ->
                                  let uu____9186 = encode_pat env1 p in
                                  (match uu____9186 with
                                   | (env0, pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2 ->
                                                 fun uu____9223 ->
                                                   match uu____9223 with
                                                   | (x, t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9230 =
                                         match w with
                                         | FStar_Pervasives_Native.None ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9252 =
                                               encode_term w1 env2 in
                                             (match uu____9252 with
                                              | (w2, decls2) ->
                                                  let uu____9265 =
                                                    let uu____9266 =
                                                      let uu____9271 =
                                                        let uu____9272 =
                                                          let uu____9277 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9277) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9272 in
                                                      (guard, uu____9271) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9266 in
                                                  (uu____9265, decls2)) in
                                       (match uu____9230 with
                                        | (guard1, decls2) ->
                                            let uu____9290 =
                                              encode_br br env2 in
                                            (match uu____9290 with
                                             | (br1, decls3) ->
                                                 let uu____9303 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9303,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9116 with
                      | (match_tm, decls1) ->
                          let uu____9322 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9322, decls1)))
and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat ->
      (env_t, pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun pat ->
      (let uu____9362 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9362
       then
         let uu____9363 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9363
       else ());
      (let uu____9365 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9365 with
       | (vars, pat_term) ->
           let uu____9382 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9435 ->
                     fun v1 ->
                       match uu____9435 with
                       | (env1, vars1) ->
                           let uu____9487 = gen_term_var env1 v1 in
                           (match uu____9487 with
                            | (xx, uu____9509, env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9382 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9588 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9589 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9590 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9598 = encode_const c env1 in
                      (match uu____9598 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu____9612::uu____9613 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9616 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9639 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9639 with
                        | (uu____9646, uu____9647::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9650 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9683 ->
                                  match uu____9683 with
                                  | (arg, uu____9691) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9697 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9697)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x, uu____9724) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9755 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let uu____9778 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9822 ->
                                  match uu____9822 with
                                  | (arg, uu____9836) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9842 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9842)) in
                      FStar_All.pipe_right uu____9778 FStar_List.flatten in
                let pat_term1 uu____9870 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and (encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,
        FStar_SMTEncoding_Term.decls_t) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    fun env ->
      let uu____9880 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9918 ->
                fun uu____9919 ->
                  match (uu____9918, uu____9919) with
                  | ((tms, decls), (t, uu____9955)) ->
                      let uu____9976 = encode_term t env in
                      (match uu____9976 with
                       | (t1, decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9880 with | (l1, decls) -> ((FStar_List.rev l1), decls)
and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    fun env ->
      let list_elements1 e =
        let uu____10033 = FStar_Syntax_Util.list_elements e in
        match uu____10033 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____10054 =
          let uu____10069 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____10069 FStar_Syntax_Util.head_and_args in
        match uu____10054 with
        | (head1, args) ->
            let uu____10108 =
              let uu____10121 =
                let uu____10122 = FStar_Syntax_Util.un_uinst head1 in
                uu____10122.FStar_Syntax_Syntax.n in
              (uu____10121, args) in
            (match uu____10108 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____10136, uu____10137)::(e, uu____10139)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10174 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10210 =
            let uu____10225 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10225 FStar_Syntax_Util.head_and_args in
          match uu____10210 with
          | (head1, args) ->
              let uu____10266 =
                let uu____10279 =
                  let uu____10280 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10280.FStar_Syntax_Syntax.n in
                (uu____10279, args) in
              (match uu____10266 with
               | (FStar_Syntax_Syntax.Tm_fvar fv, (e, uu____10297)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10324 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10346 = smt_pat_or1 t1 in
            (match uu____10346 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10362 = list_elements1 e in
                 FStar_All.pipe_right uu____10362
                   (FStar_List.map
                      (fun branch1 ->
                         let uu____10380 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10380
                           (FStar_List.map one_pat)))
             | uu____10391 ->
                 let uu____10396 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10396])
        | uu____10417 ->
            let uu____10420 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10420] in
      let uu____10441 =
        let uu____10460 =
          let uu____10461 = FStar_Syntax_Subst.compress t in
          uu____10461.FStar_Syntax_Syntax.n in
        match uu____10460 with
        | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
            let uu____10500 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10500 with
             | (binders1, c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10543;
                        FStar_Syntax_Syntax.effect_name = uu____10544;
                        FStar_Syntax_Syntax.result_typ = uu____10545;
                        FStar_Syntax_Syntax.effect_args =
                          (pre, uu____10547)::(post, uu____10549)::(pats,
                                                                    uu____10551)::[];
                        FStar_Syntax_Syntax.flags = uu____10552;_}
                      ->
                      let uu____10593 = lemma_pats pats in
                      (binders1, pre, post, uu____10593)
                  | uu____10610 -> failwith "impos"))
        | uu____10629 -> failwith "Impos" in
      match uu____10441 with
      | (binders, pre, post, patterns) ->
          let env1 =
            let uu___115_10677 = env in
            {
              bindings = (uu___115_10677.bindings);
              depth = (uu___115_10677.depth);
              tcenv = (uu___115_10677.tcenv);
              warn = (uu___115_10677.warn);
              cache = (uu___115_10677.cache);
              nolabels = (uu___115_10677.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___115_10677.encode_non_total_function_typ);
              current_module_name = (uu___115_10677.current_module_name)
            } in
          let uu____10678 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10678 with
           | (vars, guards, env2, decls, uu____10703) ->
               let uu____10716 =
                 let uu____10731 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1 ->
                           let uu____10785 =
                             let uu____10796 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1 -> encode_smt_pattern t1 env2)) in
                             FStar_All.pipe_right uu____10796
                               FStar_List.unzip in
                           match uu____10785 with
                           | (pats, decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10731 FStar_List.unzip in
               (match uu____10716 with
                | (pats, decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___116_10948 = env2 in
                      {
                        bindings = (uu___116_10948.bindings);
                        depth = (uu___116_10948.depth);
                        tcenv = (uu___116_10948.tcenv);
                        warn = (uu___116_10948.warn);
                        cache = (uu___116_10948.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___116_10948.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___116_10948.encode_non_total_function_typ);
                        current_module_name =
                          (uu___116_10948.current_module_name)
                      } in
                    let uu____10949 =
                      let uu____10954 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10954 env3 in
                    (match uu____10949 with
                     | (pre1, decls'') ->
                         let uu____10961 =
                           let uu____10966 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10966 env3 in
                         (match uu____10961 with
                          | (post2, decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10976 =
                                let uu____10977 =
                                  let uu____10988 =
                                    let uu____10989 =
                                      let uu____10994 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10994, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10989 in
                                  (pats, vars, uu____10988) in
                                FStar_SMTEncoding_Util.mkForall uu____10977 in
                              (uu____10976, decls1)))))
and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat, FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    fun env ->
      let uu____11007 = FStar_Syntax_Util.head_and_args t in
      match uu____11007 with
      | (head1, args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1 in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar fv,
              uu____11066::(x, uu____11068)::(t1, uu____11070)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11117 = encode_term x env in
               (match uu____11117 with
                | (x1, decls) ->
                    let uu____11130 = encode_term t1 env in
                    (match uu____11130 with
                     | (t2, decls') ->
                         let uu____11143 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                         (uu____11143, (FStar_List.append decls decls'))))
           | uu____11146 -> encode_term t env)
and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi ->
    fun env ->
      let debug1 phi1 =
        let uu____11169 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____11169
        then
          let uu____11170 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____11171 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11170 uu____11171
        else () in
      let enc f r l =
        let uu____11204 =
          FStar_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu____11232 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11232 with
                 | (t, decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____11204 with
        | (decls, args) ->
            let uu____11261 =
              let uu___117_11262 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11262.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11262.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11261, decls) in
      let const_op f r uu____11293 =
        let uu____11306 = f r in (uu____11306, []) in
      let un_op f l =
        let uu____11325 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11325 in
      let bin_op f uu___91_11341 =
        match uu___91_11341 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11352 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11386 =
          FStar_Util.fold_map
            (fun decls ->
               fun uu____11409 ->
                 match uu____11409 with
                 | (t, uu____11423) ->
                     let uu____11424 = encode_formula t env in
                     (match uu____11424 with
                      | (phi1, decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11386 with
        | (decls, phis) ->
            let uu____11453 =
              let uu___118_11454 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___118_11454.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___118_11454.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11453, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11515 ->
               match uu____11515 with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11534) -> false
                    | uu____11535 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11550 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11550
        else
          (let uu____11564 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11564 r rf) in
      let mk_imp1 r uu___92_11589 =
        match uu___92_11589 with
        | (lhs, uu____11595)::(rhs, uu____11597)::[] ->
            let uu____11624 = encode_formula rhs env in
            (match uu____11624 with
             | (l1, decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp, uu____11639) ->
                      (l1, decls1)
                  | uu____11644 ->
                      let uu____11645 = encode_formula lhs env in
                      (match uu____11645 with
                       | (l2, decls2) ->
                           let uu____11656 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11656, (FStar_List.append decls1 decls2)))))
        | uu____11659 -> failwith "impossible" in
      let mk_ite r uu___93_11680 =
        match uu___93_11680 with
        | (guard, uu____11686)::(_then, uu____11688)::(_else, uu____11690)::[]
            ->
            let uu____11727 = encode_formula guard env in
            (match uu____11727 with
             | (g, decls1) ->
                 let uu____11738 = encode_formula _then env in
                 (match uu____11738 with
                  | (t, decls2) ->
                      let uu____11749 = encode_formula _else env in
                      (match uu____11749 with
                       | (e, decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11763 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11788 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11788 in
      let connectives =
        let uu____11806 =
          let uu____11819 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11819) in
        let uu____11836 =
          let uu____11851 =
            let uu____11864 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11864) in
          let uu____11881 =
            let uu____11896 =
              let uu____11911 =
                let uu____11924 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11924) in
              let uu____11941 =
                let uu____11956 =
                  let uu____11971 =
                    let uu____11984 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11984) in
                  [uu____11971;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11956 in
              uu____11911 :: uu____11941 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11896 in
          uu____11851 :: uu____11881 in
        uu____11806 :: uu____11836 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) ->
            let uu____12305 = encode_formula phi' env in
            (match uu____12305 with
             | (phi2, decls) ->
                 let uu____12316 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12316, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12317 ->
            let uu____12324 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12324 env
        | FStar_Syntax_Syntax.Tm_match (e, pats) ->
            let uu____12363 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12363 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false,
              { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____12375;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____12377;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____12379;
                FStar_Syntax_Syntax.lbpos = uu____12380;_}::[]),
             e2)
            ->
            let uu____12404 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12404 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____12451::(x, uu____12453)::(t, uu____12455)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12502 = encode_term x env in
                 (match uu____12502 with
                  | (x1, decls) ->
                      let uu____12513 = encode_term t env in
                      (match uu____12513 with
                       | (t1, decls') ->
                           let uu____12524 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12524, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (r, uu____12529)::(msg, uu____12531)::(phi2, uu____12533)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12578 =
                   let uu____12583 =
                     let uu____12584 = FStar_Syntax_Subst.compress r in
                     uu____12584.FStar_Syntax_Syntax.n in
                   let uu____12587 =
                     let uu____12588 = FStar_Syntax_Subst.compress msg in
                     uu____12588.FStar_Syntax_Syntax.n in
                   (uu____12583, uu____12587) in
                 (match uu____12578 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1), FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s, uu____12597))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12603 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv, (t, uu____12610)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12635 when head_redex env head2 ->
                 let uu____12648 = whnf env phi1 in
                 encode_formula uu____12648 env
             | uu____12649 ->
                 let uu____12662 = encode_term phi1 env in
                 (match uu____12662 with
                  | (tt, decls) ->
                      let uu____12673 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___119_12676 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___119_12676.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___119_12676.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12673, decls)))
        | uu____12677 ->
            let uu____12678 = encode_term phi1 env in
            (match uu____12678 with
             | (tt, decls) ->
                 let uu____12689 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___120_12692 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___120_12692.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___120_12692.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12689, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12728 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12728 with
        | (vars, guards, env2, decls, uu____12767) ->
            let uu____12780 =
              let uu____12793 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p ->
                        let uu____12845 =
                          let uu____12856 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12896 ->
                                    match uu____12896 with
                                    | (t, uu____12910) ->
                                        encode_smt_pattern t
                                          (let uu___121_12916 = env2 in
                                           {
                                             bindings =
                                               (uu___121_12916.bindings);
                                             depth = (uu___121_12916.depth);
                                             tcenv = (uu___121_12916.tcenv);
                                             warn = (uu___121_12916.warn);
                                             cache = (uu___121_12916.cache);
                                             nolabels =
                                               (uu___121_12916.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___121_12916.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___121_12916.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12856 FStar_List.unzip in
                        match uu____12845 with
                        | (p1, decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12793 FStar_List.unzip in
            (match uu____12780 with
             | (pats, decls') ->
                 let uu____13025 = encode_formula body env2 in
                 (match uu____13025 with
                  | (body1, decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf, p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13057;
                             FStar_SMTEncoding_Term.rng = uu____13058;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____13073 -> guards in
                      let uu____13078 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____13078, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____13138 ->
                   match uu____13138 with
                   | (x, uu____13144) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____13152 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out ->
                    fun x ->
                      let uu____13164 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____13164) uu____13152 tl1 in
             let uu____13167 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13194 ->
                       match uu____13194 with
                       | (b, uu____13200) ->
                           let uu____13201 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____13201)) in
             (match uu____13167 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some (x, uu____13207) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out ->
                         fun t ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____13221 =
                    let uu____13226 =
                      let uu____13227 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13227 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13226) in
                  FStar_Errors.log_issue pos uu____13221) in
       let uu____13228 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____13228 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms))
           ->
           let uu____13237 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13295 ->
                     match uu____13295 with
                     | (l, uu____13309) -> FStar_Ident.lid_equals op l)) in
           (match uu____13237 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13342, f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13382 = encode_q_body env vars pats body in
             match uu____13382 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu____13427 =
                     let uu____13438 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13438) in
                   FStar_SMTEncoding_Term.mkForall uu____13427
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13457 = encode_q_body env vars pats body in
             match uu____13457 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu____13501 =
                   let uu____13502 =
                     let uu____13513 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13513) in
                   FStar_SMTEncoding_Term.mkExists uu____13502
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13501, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term, Prims.int,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple3
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term, Prims.int,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
let (prims : prims_t) =
  let uu____13616 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13616 with
  | (asym, a) ->
      let uu____13623 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13623 with
       | (xsym, x) ->
           let uu____13630 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13630 with
            | (ysym, y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13678 =
                      let uu____13689 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13689, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13678 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13715 =
                      let uu____13722 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13722) in
                    FStar_SMTEncoding_Util.mkApp uu____13715 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13735 =
                    let uu____13738 =
                      let uu____13741 =
                        let uu____13744 =
                          let uu____13745 =
                            let uu____13752 =
                              let uu____13753 =
                                let uu____13764 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13764) in
                              FStar_SMTEncoding_Util.mkForall uu____13753 in
                            (uu____13752, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13745 in
                        let uu____13781 =
                          let uu____13784 =
                            let uu____13785 =
                              let uu____13792 =
                                let uu____13793 =
                                  let uu____13804 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13804) in
                                FStar_SMTEncoding_Util.mkForall uu____13793 in
                              (uu____13792,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13785 in
                          [uu____13784] in
                        uu____13744 :: uu____13781 in
                      xtok_decl :: uu____13741 in
                    xname_decl :: uu____13738 in
                  (xtok1, (FStar_List.length vars), uu____13735) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13901 =
                    let uu____13916 =
                      let uu____13927 =
                        let uu____13928 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13928 in
                      quant axy uu____13927 in
                    (FStar_Parser_Const.op_Eq, uu____13916) in
                  let uu____13939 =
                    let uu____13956 =
                      let uu____13971 =
                        let uu____13982 =
                          let uu____13983 =
                            let uu____13984 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13984 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13983 in
                        quant axy uu____13982 in
                      (FStar_Parser_Const.op_notEq, uu____13971) in
                    let uu____13995 =
                      let uu____14012 =
                        let uu____14027 =
                          let uu____14038 =
                            let uu____14039 =
                              let uu____14040 =
                                let uu____14045 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____14046 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____14045, uu____14046) in
                              FStar_SMTEncoding_Util.mkLT uu____14040 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14039 in
                          quant xy uu____14038 in
                        (FStar_Parser_Const.op_LT, uu____14027) in
                      let uu____14057 =
                        let uu____14074 =
                          let uu____14089 =
                            let uu____14100 =
                              let uu____14101 =
                                let uu____14102 =
                                  let uu____14107 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____14108 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____14107, uu____14108) in
                                FStar_SMTEncoding_Util.mkLTE uu____14102 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14101 in
                            quant xy uu____14100 in
                          (FStar_Parser_Const.op_LTE, uu____14089) in
                        let uu____14119 =
                          let uu____14136 =
                            let uu____14151 =
                              let uu____14162 =
                                let uu____14163 =
                                  let uu____14164 =
                                    let uu____14169 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____14170 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____14169, uu____14170) in
                                  FStar_SMTEncoding_Util.mkGT uu____14164 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14163 in
                              quant xy uu____14162 in
                            (FStar_Parser_Const.op_GT, uu____14151) in
                          let uu____14181 =
                            let uu____14198 =
                              let uu____14213 =
                                let uu____14224 =
                                  let uu____14225 =
                                    let uu____14226 =
                                      let uu____14231 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____14232 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____14231, uu____14232) in
                                    FStar_SMTEncoding_Util.mkGTE uu____14226 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14225 in
                                quant xy uu____14224 in
                              (FStar_Parser_Const.op_GTE, uu____14213) in
                            let uu____14243 =
                              let uu____14260 =
                                let uu____14275 =
                                  let uu____14286 =
                                    let uu____14287 =
                                      let uu____14288 =
                                        let uu____14293 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____14294 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____14293, uu____14294) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14288 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14287 in
                                  quant xy uu____14286 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14275) in
                              let uu____14305 =
                                let uu____14322 =
                                  let uu____14337 =
                                    let uu____14348 =
                                      let uu____14349 =
                                        let uu____14350 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14350 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14349 in
                                    quant qx uu____14348 in
                                  (FStar_Parser_Const.op_Minus, uu____14337) in
                                let uu____14361 =
                                  let uu____14378 =
                                    let uu____14393 =
                                      let uu____14404 =
                                        let uu____14405 =
                                          let uu____14406 =
                                            let uu____14411 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14412 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14411, uu____14412) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14406 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14405 in
                                      quant xy uu____14404 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14393) in
                                  let uu____14423 =
                                    let uu____14440 =
                                      let uu____14455 =
                                        let uu____14466 =
                                          let uu____14467 =
                                            let uu____14468 =
                                              let uu____14473 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14474 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14473, uu____14474) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14468 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14467 in
                                        quant xy uu____14466 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14455) in
                                    let uu____14485 =
                                      let uu____14502 =
                                        let uu____14517 =
                                          let uu____14528 =
                                            let uu____14529 =
                                              let uu____14530 =
                                                let uu____14535 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14536 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14535, uu____14536) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14530 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14529 in
                                          quant xy uu____14528 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14517) in
                                      let uu____14547 =
                                        let uu____14564 =
                                          let uu____14579 =
                                            let uu____14590 =
                                              let uu____14591 =
                                                let uu____14592 =
                                                  let uu____14597 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14598 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14597, uu____14598) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14592 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14591 in
                                            quant xy uu____14590 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14579) in
                                        let uu____14609 =
                                          let uu____14626 =
                                            let uu____14641 =
                                              let uu____14652 =
                                                let uu____14653 =
                                                  let uu____14654 =
                                                    let uu____14659 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14660 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14659,
                                                      uu____14660) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14654 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14653 in
                                              quant xy uu____14652 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14641) in
                                          let uu____14671 =
                                            let uu____14688 =
                                              let uu____14703 =
                                                let uu____14714 =
                                                  let uu____14715 =
                                                    let uu____14716 =
                                                      let uu____14721 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14722 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14721,
                                                        uu____14722) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14716 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14715 in
                                                quant xy uu____14714 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14703) in
                                            let uu____14733 =
                                              let uu____14750 =
                                                let uu____14765 =
                                                  let uu____14776 =
                                                    let uu____14777 =
                                                      let uu____14778 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14778 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14777 in
                                                  quant qx uu____14776 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14765) in
                                              [uu____14750] in
                                            uu____14688 :: uu____14733 in
                                          uu____14626 :: uu____14671 in
                                        uu____14564 :: uu____14609 in
                                      uu____14502 :: uu____14547 in
                                    uu____14440 :: uu____14485 in
                                  uu____14378 :: uu____14423 in
                                uu____14322 :: uu____14361 in
                              uu____14260 :: uu____14305 in
                            uu____14198 :: uu____14243 in
                          uu____14136 :: uu____14181 in
                        uu____14074 :: uu____14119 in
                      uu____14012 :: uu____14057 in
                    uu____13956 :: uu____13995 in
                  uu____13901 :: uu____13939 in
                let mk1 l v1 =
                  let uu____15028 =
                    let uu____15039 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15105 ->
                              match uu____15105 with
                              | (l', uu____15121) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____15039
                      (FStar_Option.map
                         (fun uu____15193 ->
                            match uu____15193 with | (uu____15216, b) -> b v1)) in
                  FStar_All.pipe_right uu____15028 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15301 ->
                          match uu____15301 with
                          | (l', uu____15317) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let (pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string, FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun tapp ->
      fun vars ->
        let uu____15359 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____15359 with
        | (xxsym, xx) ->
            let uu____15366 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____15366 with
             | (ffsym, ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____15376 =
                   let uu____15383 =
                     let uu____15384 =
                       let uu____15395 =
                         let uu____15396 =
                           let uu____15401 =
                             let uu____15402 =
                               let uu____15407 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____15407) in
                             FStar_SMTEncoding_Util.mkEq uu____15402 in
                           (xx_has_type, uu____15401) in
                         FStar_SMTEncoding_Util.mkImp uu____15396 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15395) in
                     FStar_SMTEncoding_Util.mkForall uu____15384 in
                   let uu____15432 =
                     let uu____15433 =
                       let uu____15434 =
                         let uu____15435 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____15435 in
                       Prims.strcat module_name uu____15434 in
                     varops.mk_unique uu____15433 in
                   (uu____15383, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15432) in
                 FStar_SMTEncoding_Util.mkAssume uu____15376)
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____15471 =
      let uu____15472 =
        let uu____15479 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____15479, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15472 in
    let uu____15482 =
      let uu____15485 =
        let uu____15486 =
          let uu____15493 =
            let uu____15494 =
              let uu____15505 =
                let uu____15506 =
                  let uu____15511 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15511) in
                FStar_SMTEncoding_Util.mkImp uu____15506 in
              ([[typing_pred]], [xx], uu____15505) in
            mkForall_fuel uu____15494 in
          (uu____15493, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15486 in
      [uu____15485] in
    uu____15471 :: uu____15482 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15553 =
      let uu____15554 =
        let uu____15561 =
          let uu____15562 =
            let uu____15573 =
              let uu____15578 =
                let uu____15581 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15581] in
              [uu____15578] in
            let uu____15586 =
              let uu____15587 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15587 tt in
            (uu____15573, [bb], uu____15586) in
          FStar_SMTEncoding_Util.mkForall uu____15562 in
        (uu____15561, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15554 in
    let uu____15608 =
      let uu____15611 =
        let uu____15612 =
          let uu____15619 =
            let uu____15620 =
              let uu____15631 =
                let uu____15632 =
                  let uu____15637 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15637) in
                FStar_SMTEncoding_Util.mkImp uu____15632 in
              ([[typing_pred]], [xx], uu____15631) in
            mkForall_fuel uu____15620 in
          (uu____15619, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15612 in
      [uu____15611] in
    uu____15553 :: uu____15608 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15687 =
        let uu____15688 =
          let uu____15695 =
            let uu____15698 =
              let uu____15701 =
                let uu____15704 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15705 =
                  let uu____15708 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15708] in
                uu____15704 :: uu____15705 in
              tt :: uu____15701 in
            tt :: uu____15698 in
          ("Prims.Precedes", uu____15695) in
        FStar_SMTEncoding_Util.mkApp uu____15688 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15687 in
    let precedes_y_x =
      let uu____15712 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15712 in
    let uu____15715 =
      let uu____15716 =
        let uu____15723 =
          let uu____15724 =
            let uu____15735 =
              let uu____15740 =
                let uu____15743 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15743] in
              [uu____15740] in
            let uu____15748 =
              let uu____15749 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15749 tt in
            (uu____15735, [bb], uu____15748) in
          FStar_SMTEncoding_Util.mkForall uu____15724 in
        (uu____15723, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15716 in
    let uu____15770 =
      let uu____15773 =
        let uu____15774 =
          let uu____15781 =
            let uu____15782 =
              let uu____15793 =
                let uu____15794 =
                  let uu____15799 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15799) in
                FStar_SMTEncoding_Util.mkImp uu____15794 in
              ([[typing_pred]], [xx], uu____15793) in
            mkForall_fuel uu____15782 in
          (uu____15781, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15774 in
      let uu____15824 =
        let uu____15827 =
          let uu____15828 =
            let uu____15835 =
              let uu____15836 =
                let uu____15847 =
                  let uu____15848 =
                    let uu____15853 =
                      let uu____15854 =
                        let uu____15857 =
                          let uu____15860 =
                            let uu____15863 =
                              let uu____15864 =
                                let uu____15869 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15870 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15869, uu____15870) in
                              FStar_SMTEncoding_Util.mkGT uu____15864 in
                            let uu____15871 =
                              let uu____15874 =
                                let uu____15875 =
                                  let uu____15880 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15881 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15880, uu____15881) in
                                FStar_SMTEncoding_Util.mkGTE uu____15875 in
                              let uu____15882 =
                                let uu____15885 =
                                  let uu____15886 =
                                    let uu____15891 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15892 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15891, uu____15892) in
                                  FStar_SMTEncoding_Util.mkLT uu____15886 in
                                [uu____15885] in
                              uu____15874 :: uu____15882 in
                            uu____15863 :: uu____15871 in
                          typing_pred_y :: uu____15860 in
                        typing_pred :: uu____15857 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15854 in
                    (uu____15853, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15848 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15847) in
              mkForall_fuel uu____15836 in
            (uu____15835,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15828 in
        [uu____15827] in
      uu____15773 :: uu____15824 in
    uu____15715 :: uu____15770 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15938 =
      let uu____15939 =
        let uu____15946 =
          let uu____15947 =
            let uu____15958 =
              let uu____15963 =
                let uu____15966 = FStar_SMTEncoding_Term.boxString b in
                [uu____15966] in
              [uu____15963] in
            let uu____15971 =
              let uu____15972 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15972 tt in
            (uu____15958, [bb], uu____15971) in
          FStar_SMTEncoding_Util.mkForall uu____15947 in
        (uu____15946, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15939 in
    let uu____15993 =
      let uu____15996 =
        let uu____15997 =
          let uu____16004 =
            let uu____16005 =
              let uu____16016 =
                let uu____16017 =
                  let uu____16022 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____16022) in
                FStar_SMTEncoding_Util.mkImp uu____16017 in
              ([[typing_pred]], [xx], uu____16016) in
            mkForall_fuel uu____16005 in
          (uu____16004, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15997 in
      [uu____15996] in
    uu____15938 :: uu____15993 in
  let mk_eq2_interp nm env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____16084 =
      let uu____16085 =
        let uu____16092 =
          let uu____16093 =
            let uu____16104 =
              let uu____16105 =
                let uu____16110 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____16110, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16105 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16104) in
          FStar_SMTEncoding_Util.mkForall uu____16093 in
        (uu____16092, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          nm) in
      FStar_SMTEncoding_Util.mkAssume uu____16085 in
    [uu____16084] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____16183 =
      let uu____16184 =
        let uu____16191 =
          let uu____16192 =
            let uu____16203 =
              let uu____16204 =
                let uu____16209 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____16209, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16204 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16203) in
          FStar_SMTEncoding_Util.mkForall uu____16192 in
        (uu____16191, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16184 in
    [uu____16183] in
  let mk_forall_interp nm env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____16284 =
        let uu____16291 =
          let uu____16294 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16294] in
        ("Valid", uu____16291) in
      FStar_SMTEncoding_Util.mkApp uu____16284 in
    let uu____16297 =
      let uu____16298 =
        let uu____16305 =
          let uu____16306 =
            let uu____16317 =
              let uu____16318 =
                let uu____16323 =
                  let uu____16324 =
                    let uu____16335 =
                      let uu____16340 =
                        let uu____16343 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16343] in
                      [uu____16340] in
                    let uu____16348 =
                      let uu____16349 =
                        let uu____16354 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16354, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16349 in
                    (uu____16335, [xx1], uu____16348) in
                  FStar_SMTEncoding_Util.mkForall uu____16324 in
                (uu____16323, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16318 in
            ([[l_forall_a_b]], [aa; bb], uu____16317) in
          FStar_SMTEncoding_Util.mkForall uu____16306 in
        (uu____16305, (FStar_Pervasives_Native.Some "forall interpretation"),
          nm) in
      FStar_SMTEncoding_Util.mkAssume uu____16298 in
    [uu____16297] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____16436 =
        let uu____16443 =
          let uu____16446 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16446] in
        ("Valid", uu____16443) in
      FStar_SMTEncoding_Util.mkApp uu____16436 in
    let uu____16449 =
      let uu____16450 =
        let uu____16457 =
          let uu____16458 =
            let uu____16469 =
              let uu____16470 =
                let uu____16475 =
                  let uu____16476 =
                    let uu____16487 =
                      let uu____16492 =
                        let uu____16495 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16495] in
                      [uu____16492] in
                    let uu____16500 =
                      let uu____16501 =
                        let uu____16506 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16506, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16501 in
                    (uu____16487, [xx1], uu____16500) in
                  FStar_SMTEncoding_Util.mkExists uu____16476 in
                (uu____16475, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16470 in
            ([[l_exists_a_b]], [aa; bb], uu____16469) in
          FStar_SMTEncoding_Util.mkForall uu____16458 in
        (uu____16457, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16450 in
    [uu____16449] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16566 =
      let uu____16567 =
        let uu____16574 =
          let uu____16575 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16575 range_ty in
        let uu____16576 = varops.mk_unique "typing_range_const" in
        (uu____16574, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16576) in
      FStar_SMTEncoding_Util.mkAssume uu____16567 in
    [uu____16566] in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____16610 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16610 x1 t in
      let uu____16611 =
        let uu____16622 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16622) in
      FStar_SMTEncoding_Util.mkForall uu____16611 in
    let uu____16645 =
      let uu____16646 =
        let uu____16653 =
          let uu____16654 =
            let uu____16665 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16665) in
          FStar_SMTEncoding_Util.mkForall uu____16654 in
        (uu____16653,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16646 in
    [uu____16645] in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e]) in
    let uu____16715 =
      let uu____16716 =
        let uu____16723 =
          let uu____16724 =
            let uu____16739 =
              let uu____16740 =
                let uu____16745 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____16746 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____16745, uu____16746) in
              FStar_SMTEncoding_Util.mkAnd uu____16740 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16739) in
          FStar_SMTEncoding_Util.mkForall' uu____16724 in
        (uu____16723,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____16716 in
    [uu____16715] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.t_eq2_lid, (mk_eq2_interp "t_eq2-interp"));
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.t_forall_lid, (mk_forall_interp "t_forall-interp"));
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)] in
  fun env ->
    fun t ->
      fun s ->
        fun tt ->
          let uu____16980 =
            FStar_Util.find_opt
              (fun uu____17006 ->
                 match uu____17006 with
                 | (l, uu____17018) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16980 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some (uu____17043, f) -> f env s tt
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env ->
    fun fv ->
      fun t ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17079 = encode_function_type_as_formula t env in
        match uu____17079 with
        | (form, decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let (encode_free_var :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list, env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted ->
    fun env ->
      fun fv ->
        fun tt ->
          fun t_norm ->
            fun quals ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu____17119 =
                ((let uu____17122 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17122) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17119
              then
                let arg_sorts =
                  let uu____17132 =
                    let uu____17133 = FStar_Syntax_Subst.compress t_norm in
                    uu____17133.FStar_Syntax_Syntax.n in
                  match uu____17132 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders, uu____17139) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____17169 ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____17174 -> [] in
                let arity = FStar_List.length arg_sorts in
                let uu____17176 =
                  new_term_constant_and_tok_from_lid env lid arity in
                match uu____17176 with
                | (vname, vtok, env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    ([d; dd], env1)
              else
                (let uu____17209 = prims.is lid in
                 if uu____17209
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17217 = prims.mk lid vname in
                   match uu____17217 with
                   | (tok, arity, definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17244 =
                      let uu____17255 = curried_arrow_formals_comp t_norm in
                      match uu____17255 with
                      | (args, comp) ->
                          let comp1 =
                            let uu____17273 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17273
                            then
                              let uu____17274 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___122_17277 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___122_17277.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___122_17277.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___122_17277.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___122_17277.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___122_17277.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___122_17277.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___122_17277.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___122_17277.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___122_17277.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___122_17277.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___122_17277.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___122_17277.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___122_17277.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___122_17277.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___122_17277.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___122_17277.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___122_17277.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___122_17277.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___122_17277.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___122_17277.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___122_17277.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___122_17277.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___122_17277.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___122_17277.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___122_17277.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___122_17277.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___122_17277.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___122_17277.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___122_17277.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___122_17277.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___122_17277.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___122_17277.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___122_17277.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___122_17277.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___122_17277.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17274
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17289 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17289)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17244 with
                    | (formals, (pre_opt, res_t)) ->
                        let arity = FStar_List.length formals in
                        let uu____17339 =
                          new_term_constant_and_tok_from_lid env lid arity in
                        (match uu____17339 with
                         | (vname, vtok, env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17364 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___94_17406 ->
                                       match uu___94_17406 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17410 =
                                             FStar_Util.prefix vars in
                                           (match uu____17410 with
                                            | (uu____17431,
                                               (xxsym, uu____17433)) ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17451 =
                                                  let uu____17452 =
                                                    let uu____17459 =
                                                      let uu____17460 =
                                                        let uu____17471 =
                                                          let uu____17472 =
                                                            let uu____17477 =
                                                              let uu____17478
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17478 in
                                                            (vapp,
                                                              uu____17477) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17472 in
                                                        ([[vapp]], vars,
                                                          uu____17471) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17460 in
                                                    (uu____17459,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17452 in
                                                [uu____17451])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d, f) ->
                                           let uu____17497 =
                                             FStar_Util.prefix vars in
                                           (match uu____17497 with
                                            | (uu____17518,
                                               (xxsym, uu____17520)) ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  } in
                                                let tp_name =
                                                  mk_term_projector_name d f1 in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx]) in
                                                let uu____17543 =
                                                  let uu____17544 =
                                                    let uu____17551 =
                                                      let uu____17552 =
                                                        let uu____17563 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17563) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17552 in
                                                    (uu____17551,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17544 in
                                                [uu____17543])
                                       | uu____17580 -> [])) in
                             let uu____17581 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17581 with
                              | (vars, guards, env', decls1, uu____17608) ->
                                  let uu____17621 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None ->
                                        let uu____17630 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17630, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17632 =
                                          encode_formula p env' in
                                        (match uu____17632 with
                                         | (g, ds) ->
                                             let uu____17643 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17643,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17621 with
                                   | (guard, decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17656 =
                                           let uu____17663 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17663) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17656 in
                                       let uu____17672 =
                                         let vname_decl =
                                           let uu____17680 =
                                             let uu____17691 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17701 ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17691,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17680 in
                                         let uu____17710 =
                                           let env2 =
                                             let uu___123_17716 = env1 in
                                             {
                                               bindings =
                                                 (uu___123_17716.bindings);
                                               depth = (uu___123_17716.depth);
                                               tcenv = (uu___123_17716.tcenv);
                                               warn = (uu___123_17716.warn);
                                               cache = (uu___123_17716.cache);
                                               nolabels =
                                                 (uu___123_17716.nolabels);
                                               use_zfuel_name =
                                                 (uu___123_17716.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___123_17716.current_module_name)
                                             } in
                                           let uu____17717 =
                                             let uu____17718 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17718 in
                                           if uu____17717
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17710 with
                                         | (tok_typing, decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17733::uu____17734 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort) in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff] in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)] in
                                                   let guarded_tok_typing =
                                                     let uu____17774 =
                                                       let uu____17785 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17785) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17774 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17812 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17815 =
                                               match formals with
                                               | [] ->
                                                   let uu____17832 =
                                                     let uu____17833 =
                                                       let uu____17836 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_41 ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17836 in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____17833 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17832)
                                               | uu____17845 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17852 =
                                                       let uu____17859 =
                                                         let uu____17860 =
                                                           let uu____17871 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17871) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17860 in
                                                       (uu____17859,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17852 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17815 with
                                              | (tok_decl, env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17672 with
                                        | (decls2, env2) ->
                                            let uu____17914 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17922 =
                                                encode_term res_t1 env' in
                                              match uu____17922 with
                                              | (encoded_res_t, decls) ->
                                                  let uu____17935 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17935, decls) in
                                            (match uu____17914 with
                                             | (encoded_res_t, ty_pred,
                                                decls3) ->
                                                 let typingAx =
                                                   let uu____17946 =
                                                     let uu____17953 =
                                                       let uu____17954 =
                                                         let uu____17965 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17965) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17954 in
                                                     (uu____17953,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17946 in
                                                 let freshness =
                                                   let uu____17981 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17981
                                                   then
                                                     let uu____17986 =
                                                       let uu____17987 =
                                                         let uu____17998 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____18009 =
                                                           varops.next_id () in
                                                         (vname, uu____17998,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____18009) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17987 in
                                                     let uu____18012 =
                                                       let uu____18015 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____18015] in
                                                     uu____17986 ::
                                                       uu____18012
                                                   else [] in
                                                 let g =
                                                   let uu____18020 =
                                                     let uu____18023 =
                                                       let uu____18026 =
                                                         let uu____18029 =
                                                           let uu____18032 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____18032 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____18029 in
                                                       FStar_List.append
                                                         decls3 uu____18026 in
                                                     FStar_List.append decls2
                                                       uu____18023 in
                                                   FStar_List.append decls11
                                                     uu____18020 in
                                                 (g, env2))))))))
let (declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (fvar_binding, FStar_SMTEncoding_Term.decl Prims.list, env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun x ->
      fun t ->
        fun t_norm ->
          let uu____18057 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18057 with
          | FStar_Pervasives_Native.None ->
              let uu____18068 = encode_free_var false env x t t_norm [] in
              (match uu____18068 with
               | (decls, env1) ->
                   let fvb =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
let (encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list, env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted ->
    fun env ->
      fun lid ->
        fun t ->
          fun quals ->
            let tt = norm env t in
            let uu____18121 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18121 with
            | (decls, env1) ->
                let uu____18140 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18140
                then
                  let uu____18147 =
                    let uu____18150 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18150 in
                  (uu____18147, env1)
                else (decls, env1)
let (encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list, env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bindings ->
      fun quals ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18202 ->
                fun lb ->
                  match uu____18202 with
                  | (decls, env1) ->
                      let uu____18222 =
                        let uu____18229 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18229
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18222 with
                       | (decls', env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18250 = FStar_Syntax_Util.head_and_args t in
    match uu____18250 with
    | (hd1, args) ->
        let uu____18287 =
          let uu____18288 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18288.FStar_Syntax_Syntax.n in
        (match uu____18287 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18292, c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18311 -> false)
let (encode_top_level_let :
  env_t ->
    (Prims.bool, FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list, env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun uu____18333 ->
      fun quals ->
        match uu____18333 with
        | (is_rec, bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18409 = FStar_Util.first_N nbinders formals in
              match uu____18409 with
              | (formals1, extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18490 ->
                         fun uu____18491 ->
                           match (uu____18490, uu____18491) with
                           | ((formal, uu____18509), (binder, uu____18511))
                               ->
                               let uu____18520 =
                                 let uu____18527 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18527) in
                               FStar_Syntax_Syntax.NT uu____18520) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18535 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18566 ->
                              match uu____18566 with
                              | (x, i) ->
                                  let uu____18577 =
                                    let uu___124_18578 = x in
                                    let uu____18579 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___124_18578.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___124_18578.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18579
                                    } in
                                  (uu____18577, i))) in
                    FStar_All.pipe_right uu____18535
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18597 =
                      let uu____18598 = FStar_Syntax_Subst.compress body in
                      let uu____18599 =
                        let uu____18600 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18600 in
                      FStar_Syntax_Syntax.extend_app_n uu____18598
                        uu____18599 in
                    uu____18597 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18661 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18661
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___125_18664 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___125_18664.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___125_18664.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___125_18664.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___125_18664.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___125_18664.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___125_18664.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___125_18664.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___125_18664.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___125_18664.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___125_18664.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___125_18664.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___125_18664.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___125_18664.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___125_18664.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___125_18664.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___125_18664.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___125_18664.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___125_18664.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___125_18664.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___125_18664.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___125_18664.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___125_18664.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___125_18664.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___125_18664.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___125_18664.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___125_18664.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___125_18664.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___125_18664.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___125_18664.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___125_18664.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___125_18664.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___125_18664.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___125_18664.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___125_18664.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___125_18664.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18697 = FStar_Syntax_Util.abs_formals e in
                match uu____18697 with
                | (binders, body, lopt) ->
                    (match binders with
                     | uu____18761::uu____18762 ->
                         let uu____18777 =
                           let uu____18778 =
                             let uu____18781 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18781 in
                           uu____18778.FStar_Syntax_Syntax.n in
                         (match uu____18777 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals, c) ->
                              let uu____18824 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18824 with
                               | (formals1, c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18866 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18866
                                   then
                                     let uu____18901 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18901 with
                                      | (bs0, rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18995 ->
                                                   fun uu____18996 ->
                                                     match (uu____18995,
                                                             uu____18996)
                                                     with
                                                     | ((x, uu____19014),
                                                        (b, uu____19016)) ->
                                                         let uu____19025 =
                                                           let uu____19032 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19032) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19025)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19034 =
                                            let uu____19055 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19055) in
                                          (uu____19034, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19123 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19123 with
                                        | (binders1, body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x, uu____19212) ->
                              let uu____19217 =
                                let uu____19238 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19238 in
                              (uu____19217, true)
                          | uu____19303 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____19305 ->
                              let uu____19306 =
                                let uu____19307 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19308 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19307
                                  uu____19308 in
                              failwith uu____19306)
                     | uu____19333 ->
                         let rec aux' t_norm2 =
                           let uu____19358 =
                             let uu____19359 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19359.FStar_Syntax_Syntax.n in
                           match uu____19358 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals, c) ->
                               let uu____19400 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19400 with
                                | (formals1, c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19428 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19428 with
                                     | (binders1, body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv, uu____19508)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19513 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19569 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19569
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19581 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19644 ->
                            fun lb ->
                              match uu____19644 with
                              | (toks, typs, decls, env1) ->
                                  ((let uu____19699 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19699
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19702 =
                                      let uu____19711 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19711
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19702 with
                                    | (tok, decl, env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19581 with
                  | (toks, typs, decls, env1) ->
                      let toks_fvbs = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____19826 =
                          if fvb.smt_arity = (Prims.parse_int "0")
                          then
                            FStar_SMTEncoding_Util.mkFreeV
                              ((fvb.smt_id),
                                FStar_SMTEncoding_Term.Term_sort)
                          else
                            raise_arity_mismatch fvb.smt_id fvb.smt_arity
                              (Prims.parse_int "0") rng in
                        match vars with
                        | [] -> mk_fv ()
                        | uu____19832 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None ->
                                   let uu____19840 = mk_fv () in
                                   mk_Apply uu____19840 vars)
                            else
                              (let uu____19842 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____19842) in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19894;
                             FStar_Syntax_Syntax.lbeff = uu____19895;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____19897;
                             FStar_Syntax_Syntax.lbpos = uu____19898;_}::[],
                           t_norm::[], fvb::[]) ->
                            let flid = fvb.fvar_lid in
                            let uu____19922 =
                              let uu____19929 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19929 with
                              | (tcenv', uu____19947, e_t) ->
                                  let uu____19953 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19964 -> failwith "Impossible" in
                                  (match uu____19953 with
                                   | (e1, t_norm1) ->
                                       ((let uu___128_19980 = env2 in
                                         {
                                           bindings =
                                             (uu___128_19980.bindings);
                                           depth = (uu___128_19980.depth);
                                           tcenv = tcenv';
                                           warn = (uu___128_19980.warn);
                                           cache = (uu___128_19980.cache);
                                           nolabels =
                                             (uu___128_19980.nolabels);
                                           use_zfuel_name =
                                             (uu___128_19980.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___128_19980.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___128_19980.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19922 with
                             | (env', e1, t_norm1) ->
                                 let uu____19990 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____19990 with
                                  | ((binders, body, uu____20011, t_body),
                                     curry) ->
                                      let is_prop =
                                        let uu____20023 =
                                          let uu____20024 =
                                            FStar_Syntax_Subst.compress
                                              t_body in
                                          uu____20024.FStar_Syntax_Syntax.n in
                                        match uu____20023 with
                                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                                            FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.prop_lid
                                        | uu____20028 -> false in
                                      let is_lbname_squash =
                                        match lbn with
                                        | FStar_Util.Inl uu____20030 -> false
                                        | FStar_Util.Inr fv ->
                                            (FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.squash_lid)
                                              ||
                                              (FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Parser_Const.auto_squash_lid) in
                                      ((let uu____20033 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20033
                                        then
                                          let uu____20034 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20035 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20034 uu____20035
                                        else ());
                                       (let uu____20037 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20037 with
                                        | (vars, guards, env'1, binder_decls,
                                           uu____20064) ->
                                            let body1 =
                                              let uu____20078 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20078
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None) in
                                            let app =
                                              let uu____20095 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn in
                                              mk_app1 uu____20095 curry fvb
                                                vars in
                                            let uu____20096 =
                                              encode_term body1 env'1 in
                                            (match uu____20096 with
                                             | (body', decls2) ->
                                                 let eqn =
                                                   let uu____20110 =
                                                     let uu____20117 =
                                                       let uu____20118 =
                                                         let uu____20129 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body') in
                                                         ([[app]], vars,
                                                           uu____20129) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20118 in
                                                     let uu____20140 =
                                                       let uu____20143 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20143 in
                                                     (uu____20117,
                                                       uu____20140,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20110 in
                                                 let eqns =
                                                   if
                                                     is_prop &&
                                                       (Prims.op_Negation
                                                          is_lbname_squash)
                                                   then
                                                     ((let uu____20152 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env2.tcenv)
                                                           (FStar_Options.Other
                                                              "SMTEncoding") in
                                                       if uu____20152
                                                       then
                                                         let uu____20153 =
                                                           FStar_Syntax_Print.lbname_to_string
                                                             lbn in
                                                         FStar_Util.print1
                                                           "is_prop %s\n"
                                                           uu____20153
                                                       else ());
                                                      (let uu____20155 =
                                                         let uu____20164 =
                                                           FStar_SMTEncoding_Term.mk_Valid
                                                             app in
                                                         let uu____20165 =
                                                           encode_formula
                                                             body1 env'1 in
                                                         (uu____20164,
                                                           uu____20165) in
                                                       match uu____20155 with
                                                       | (app1,
                                                          (body'1, decls21))
                                                           ->
                                                           let eqn1 =
                                                             let uu____20184
                                                               =
                                                               let uu____20191
                                                                 =
                                                                 let uu____20192
                                                                   =
                                                                   let uu____20203
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body'1) in
                                                                   ([[app1]],
                                                                    vars,
                                                                    uu____20203) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____20192 in
                                                               let uu____20214
                                                                 =
                                                                 let uu____20217
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Valid Equation for %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____20217 in
                                                               (uu____20191,
                                                                 uu____20214,
                                                                 (Prims.strcat
                                                                    "valid_equation_"
                                                                    fvb.smt_id)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____20184 in
                                                           [eqn1]))
                                                   else [] in
                                                 let uu____20221 =
                                                   let uu____20224 =
                                                     let uu____20227 =
                                                       let uu____20230 =
                                                         let uu____20233 =
                                                           let uu____20236 =
                                                             primitive_type_axioms
                                                               env2.tcenv
                                                               flid
                                                               fvb.smt_id app in
                                                           FStar_List.append
                                                             eqns uu____20236 in
                                                         FStar_List.append
                                                           [eqn] uu____20233 in
                                                       FStar_List.append
                                                         decls2 uu____20230 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20227 in
                                                   FStar_List.append decls1
                                                     uu____20224 in
                                                 (uu____20221, env2))))))
                        | uu____20241 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____20296 = varops.fresh "fuel" in
                          (uu____20296, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20299 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____20346 ->
                                  fun fvb ->
                                    match uu____20346 with
                                    | (gtoks, env3) ->
                                        let flid = fvb.fvar_lid in
                                        let g =
                                          let uu____20392 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20392 in
                                        let gtok =
                                          let uu____20394 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20394 in
                                        let env4 =
                                          let uu____20396 =
                                            let uu____20399 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_42 ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_42) uu____20399 in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____20396 in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2)) in
                        match uu____20299 with
                        | (gtoks, env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20499 t_norm
                              uu____20501 =
                              match (uu____20499, uu____20501) with
                              | ((fvb, g, gtok),
                                 { FStar_Syntax_Syntax.lbname = lbn;
                                   FStar_Syntax_Syntax.lbunivs = uvs;
                                   FStar_Syntax_Syntax.lbtyp = uu____20531;
                                   FStar_Syntax_Syntax.lbeff = uu____20532;
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs = uu____20534;
                                   FStar_Syntax_Syntax.lbpos = uu____20535;_})
                                  ->
                                  let uu____20556 =
                                    let uu____20563 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20563 with
                                    | (tcenv', uu____20585, e_t) ->
                                        let uu____20591 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20602 ->
                                              failwith "Impossible" in
                                        (match uu____20591 with
                                         | (e1, t_norm1) ->
                                             ((let uu___129_20618 = env3 in
                                               {
                                                 bindings =
                                                   (uu___129_20618.bindings);
                                                 depth =
                                                   (uu___129_20618.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___129_20618.warn);
                                                 cache =
                                                   (uu___129_20618.cache);
                                                 nolabels =
                                                   (uu___129_20618.nolabels);
                                                 use_zfuel_name =
                                                   (uu___129_20618.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___129_20618.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___129_20618.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20556 with
                                   | (env', e1, t_norm1) ->
                                       ((let uu____20633 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20633
                                         then
                                           let uu____20634 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20635 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20636 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20634 uu____20635
                                             uu____20636
                                         else ());
                                        (let uu____20638 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1 in
                                         match uu____20638 with
                                         | ((binders, body, formals, tres),
                                            curry) ->
                                             ((let uu____20675 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20675
                                               then
                                                 let uu____20676 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20677 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20678 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20679 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20676 uu____20677
                                                   uu____20678 uu____20679
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20683 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20683 with
                                               | (vars, guards, env'1,
                                                  binder_decls, uu____20714)
                                                   ->
                                                   let decl_g =
                                                     let uu____20728 =
                                                       let uu____20739 =
                                                         let uu____20742 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20742 in
                                                       (g, uu____20739,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20728 in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       fvb.fvar_lid g in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications")) in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars in
                                                   let app =
                                                     let uu____20767 =
                                                       let uu____20774 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       ((fvb.smt_id),
                                                         uu____20774) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20767 in
                                                   let gsapp =
                                                     let uu____20784 =
                                                       let uu____20791 =
                                                         let uu____20794 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____20794 ::
                                                           vars_tm in
                                                       (g, uu____20791) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20784 in
                                                   let gmax =
                                                     let uu____20800 =
                                                       let uu____20807 =
                                                         let uu____20810 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____20810 ::
                                                           vars_tm in
                                                       (g, uu____20807) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20800 in
                                                   let body1 =
                                                     let uu____20816 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____20816
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____20818 =
                                                     encode_term body1 env'1 in
                                                   (match uu____20818 with
                                                    | (body_tm, decls2) ->
                                                        let eqn_g =
                                                          let uu____20836 =
                                                            let uu____20843 =
                                                              let uu____20844
                                                                =
                                                                let uu____20859
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20859) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20844 in
                                                            let uu____20880 =
                                                              let uu____20883
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20883 in
                                                            (uu____20843,
                                                              uu____20880,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20836 in
                                                        let eqn_f =
                                                          let uu____20887 =
                                                            let uu____20894 =
                                                              let uu____20895
                                                                =
                                                                let uu____20906
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20906) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20895 in
                                                            (uu____20894,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20887 in
                                                        let eqn_g' =
                                                          let uu____20920 =
                                                            let uu____20927 =
                                                              let uu____20928
                                                                =
                                                                let uu____20939
                                                                  =
                                                                  let uu____20940
                                                                    =
                                                                    let uu____20945
                                                                    =
                                                                    let uu____20946
                                                                    =
                                                                    let uu____20953
                                                                    =
                                                                    let uu____20956
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0") in
                                                                    uu____20956
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____20953) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20946 in
                                                                    (gsapp,
                                                                    uu____20945) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____20940 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20939) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20928 in
                                                            (uu____20927,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20920 in
                                                        let uu____20979 =
                                                          let uu____20988 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____20988
                                                          with
                                                          | (vars1, v_guards,
                                                             env4,
                                                             binder_decls1,
                                                             uu____21017) ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____21042
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21042
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21047
                                                                  =
                                                                  let uu____21054
                                                                    =
                                                                    let uu____21055
                                                                    =
                                                                    let uu____21066
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21066) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21055 in
                                                                  (uu____21054,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21047 in
                                                              let uu____21087
                                                                =
                                                                let uu____21094
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21094
                                                                with
                                                                | (g_typing,
                                                                   d3) ->
                                                                    let uu____21107
                                                                    =
                                                                    let uu____21110
                                                                    =
                                                                    let uu____21111
                                                                    =
                                                                    let uu____21118
                                                                    =
                                                                    let uu____21119
                                                                    =
                                                                    let uu____21130
                                                                    =
                                                                    let uu____21131
                                                                    =
                                                                    let uu____21136
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21136,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21131 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21130) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21119 in
                                                                    (uu____21118,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21111 in
                                                                    [uu____21110] in
                                                                    (d3,
                                                                    uu____21107) in
                                                              (match uu____21087
                                                               with
                                                               | (aux_decls,
                                                                  typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____20979
                                                         with
                                                         | (aux_decls,
                                                            g_typing) ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                               (FStar_List.append
                                                                  [eqn_g;
                                                                  eqn_g';
                                                                  eqn_f]
                                                                  g_typing),
                                                               env02)))))))) in
                            let uu____21201 =
                              let uu____21214 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21275 ->
                                   fun uu____21276 ->
                                     match (uu____21275, uu____21276) with
                                     | ((decls2, eqns, env01),
                                        (gtok, ty, lb)) ->
                                         let uu____21401 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21401 with
                                          | (decls', eqns', env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21214 in
                            (match uu____21201 with
                             | (decls2, eqns, env01) ->
                                 let uu____21474 =
                                   let isDeclFun uu___95_21486 =
                                     match uu___95_21486 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21487 -> true
                                     | uu____21498 -> false in
                                   let uu____21499 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21499
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21474 with
                                  | (prefix_decls, rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21539 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___96_21543 ->
                                 match uu___96_21543 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect ->
                                     true
                                 | uu____21544 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t ->
                                   let uu____21550 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21550))) in
                      if uu____21539
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks_fvbs
                               env1
                           else
                             encode_rec_lbdefs bindings typs1 toks_fvbs env1
                         with | Inner_let_rec -> (decls1, env1)))
             with
             | Let_rec_unencodeable ->
                 let msg =
                   let uu____21602 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21602
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec (encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t, env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let nm =
        let uu____21651 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21651 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21655 = encode_sigelt' env se in
      match uu____21655 with
      | (g, env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21671 =
                  let uu____21672 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21672 in
                [uu____21671]
            | uu____21673 ->
                let uu____21674 =
                  let uu____21677 =
                    let uu____21678 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21678 in
                  uu____21677 :: g in
                let uu____21679 =
                  let uu____21682 =
                    let uu____21683 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21683 in
                  [uu____21682] in
                FStar_List.append uu____21674 uu____21679 in
          (g1, env1)
and (encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t, env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let is_opaque_to_smt t =
        let uu____21696 =
          let uu____21697 = FStar_Syntax_Subst.compress t in
          uu____21697.FStar_Syntax_Syntax.n in
        match uu____21696 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s, uu____21701)) -> s = "opaque_to_smt"
        | uu____21702 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21707 =
          let uu____21708 = FStar_Syntax_Subst.compress t in
          uu____21708.FStar_Syntax_Syntax.n in
        match uu____21707 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s, uu____21712)) -> s = "uninterpreted_by_smt"
        | uu____21713 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21718 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____21723 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21728 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21731 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21734 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21749 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21753 =
            let uu____21754 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____21754 Prims.op_Negation in
          if uu____21753
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____21780 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____21800 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ in
               match uu____21800 with
               | (formals, uu____21818) ->
                   let arity = FStar_List.length formals in
                   let uu____21836 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity in
                   (match uu____21836 with
                    | (aname, atok, env2) ->
                        let uu____21856 =
                          let uu____21861 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____21861 env2 in
                        (match uu____21856 with
                         | (tm, decls) ->
                             let a_decls =
                               let uu____21873 =
                                 let uu____21874 =
                                   let uu____21885 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21901 ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____21885,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____21874 in
                               [uu____21873;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____21914 =
                               let aux uu____21966 uu____21967 =
                                 match (uu____21966, uu____21967) with
                                 | ((bv, uu____22019),
                                    (env3, acc_sorts, acc)) ->
                                     let uu____22057 = gen_term_var env3 bv in
                                     (match uu____22057 with
                                      | (xxsym, xx, env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____21914 with
                              | (uu____22129, xs_sorts, xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22152 =
                                      let uu____22159 =
                                        let uu____22160 =
                                          let uu____22171 =
                                            let uu____22172 =
                                              let uu____22177 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22177) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22172 in
                                          ([[app]], xs_sorts, uu____22171) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22160 in
                                      (uu____22159,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22152 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22197 =
                                      let uu____22204 =
                                        let uu____22205 =
                                          let uu____22216 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22216) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22205 in
                                      (uu____22204,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22197 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22235 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22235 with
             | (env1, decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22263, uu____22264)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22265 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4") in
          (match uu____22265 with | (tname, ttok, env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22282, t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22288 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___97_22292 ->
                      match uu___97_22292 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | FStar_Syntax_Syntax.Projector uu____22293 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22298 -> true
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____22299 -> false)) in
            Prims.op_Negation uu____22288 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22308 =
               let uu____22315 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22315 env fv t quals in
             match uu____22308 with
             | (decls, env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22330 =
                   let uu____22333 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22333 in
                 (uu____22330, env1))
      | FStar_Syntax_Syntax.Sig_assume (l, us, f) ->
          let uu____22341 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22341 with
           | (uu____22350, f1) ->
               let uu____22352 = encode_formula f1 env in
               (match uu____22352 with
                | (f2, decls) ->
                    let g =
                      let uu____22366 =
                        let uu____22367 =
                          let uu____22374 =
                            let uu____22377 =
                              let uu____22378 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22378 in
                            FStar_Pervasives_Native.Some uu____22377 in
                          let uu____22379 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22374, uu____22379) in
                        FStar_SMTEncoding_Util.mkAssume uu____22367 in
                      [uu____22366] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____22385) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22397 =
            FStar_Util.fold_map
              (fun env1 ->
                 fun lb ->
                   let lid =
                     let uu____22415 =
                       let uu____22418 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22418.FStar_Syntax_Syntax.fv_name in
                     uu____22415.FStar_Syntax_Syntax.v in
                   let uu____22419 =
                     let uu____22420 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22420 in
                   if uu____22419
                   then
                     let val_decl =
                       let uu___132_22448 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___132_22448.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___132_22448.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___132_22448.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22453 = encode_sigelt' env1 val_decl in
                     match uu____22453 with | (decls, env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22397 with
           | (env1, decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22481,
            { FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2p1;
              FStar_Syntax_Syntax.lbunivs = uu____22483;
              FStar_Syntax_Syntax.lbtyp = uu____22484;
              FStar_Syntax_Syntax.lbeff = uu____22485;
              FStar_Syntax_Syntax.lbdef = uu____22486;
              FStar_Syntax_Syntax.lbattrs = uu____22487;
              FStar_Syntax_Syntax.lbpos = uu____22488;_}::[]),
           uu____22489)
          when FStar_Syntax_Syntax.fv_eq_lid b2p1 FStar_Parser_Const.b2p_lid
          ->
          let uu____22512 =
            new_term_constant_and_tok_from_lid env
              (b2p1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1") in
          (match uu____22512 with
           | (tname, ttok, env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2p_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2p", [x]) in
               let valid_b2p_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2p_x]) in
               let decls =
                 let uu____22541 =
                   let uu____22544 =
                     let uu____22545 =
                       let uu____22552 =
                         let uu____22553 =
                           let uu____22564 =
                             let uu____22565 =
                               let uu____22570 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2p_x, uu____22570) in
                             FStar_SMTEncoding_Util.mkEq uu____22565 in
                           ([[b2p_x]], [xx], uu____22564) in
                         FStar_SMTEncoding_Util.mkForall uu____22553 in
                       (uu____22552,
                         (FStar_Pervasives_Native.Some "b2p def"), "b2p_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22545 in
                   [uu____22544] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22541 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22603, uu____22604) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___98_22613 ->
                  match uu___98_22613 with
                  | FStar_Syntax_Syntax.Discriminator uu____22614 -> true
                  | uu____22615 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22618, lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l ->
                   let uu____22629 =
                     let uu____22630 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22630.FStar_Ident.idText in
                   uu____22629 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___99_22634 ->
                     match uu___99_22634 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                         -> true
                     | uu____22635 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____22639) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_22656 ->
                  match uu___100_22656 with
                  | FStar_Syntax_Syntax.Projector uu____22657 -> true
                  | uu____22662 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22665 = try_lookup_free_var env l in
          (match uu____22665 with
           | FStar_Pervasives_Native.Some uu____22672 -> ([], env)
           | FStar_Pervasives_Native.None ->
               let se1 =
                 let uu___133_22676 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_22676.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_22676.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___133_22676.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____22683) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____22701) ->
          let uu____22710 = encode_sigelts env ses in
          (match uu____22710 with
           | (g, env1) ->
               let uu____22727 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___101_22750 ->
                         match uu___101_22750 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22751;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22752;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22753;_}
                             -> false
                         | uu____22756 -> true)) in
               (match uu____22727 with
                | (g', inversions) ->
                    let uu____22771 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___102_22792 ->
                              match uu___102_22792 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22793 ->
                                  true
                              | uu____22804 -> false)) in
                    (match uu____22771 with
                     | (decls, rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t, uu____22822, tps, k, uu____22825, datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_assumption =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___103_22842 ->
                    match uu___103_22842 with
                    | FStar_Syntax_Syntax.Assumption -> true
                    | uu____22843 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_assumption
            then
              let uu____22852 = c in
              match uu____22852 with
              | (name, args, uu____22857, uu____22858, uu____22859) ->
                  let uu____22864 =
                    let uu____22865 =
                      let uu____22876 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22893 ->
                                match uu____22893 with
                                | (uu____22900, sort, uu____22902) -> sort)) in
                      (name, uu____22876, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____22865 in
                  [uu____22864]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____22929 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l ->
                      let uu____22935 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____22935 FStar_Option.isNone)) in
            if uu____22929
            then []
            else
              (let uu____22967 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____22967 with
               | (xxsym, xx) ->
                   let uu____22976 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23015 ->
                             fun l ->
                               match uu____23015 with
                               | (out, decls) ->
                                   let uu____23035 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23035 with
                                    | (uu____23046, data_t) ->
                                        let uu____23048 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23048 with
                                         | (args, res) ->
                                             let indices =
                                               let uu____23094 =
                                                 let uu____23095 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23095.FStar_Syntax_Syntax.n in
                                               match uu____23094 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23106, indices) ->
                                                   indices
                                               | uu____23128 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1 ->
                                                       fun uu____23152 ->
                                                         match uu____23152
                                                         with
                                                         | (x, uu____23158)
                                                             ->
                                                             let uu____23159
                                                               =
                                                               let uu____23160
                                                                 =
                                                                 let uu____23167
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23167,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23160 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23159)
                                                    env) in
                                             let uu____23170 =
                                               encode_args indices env1 in
                                             (match uu____23170 with
                                              | (indices1, decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____23196 =
                                                        FStar_List.map2
                                                          (fun v1 ->
                                                             fun a ->
                                                               let uu____23212
                                                                 =
                                                                 let uu____23217
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23217,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23212)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23196
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23220 =
                                                      let uu____23221 =
                                                        let uu____23226 =
                                                          let uu____23227 =
                                                            let uu____23232 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23232,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23227 in
                                                        (out, uu____23226) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23221 in
                                                    (uu____23220,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____22976 with
                    | (data_ax, decls) ->
                        let uu____23245 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23245 with
                         | (ffsym, ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23256 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23256 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23260 =
                                 let uu____23267 =
                                   let uu____23268 =
                                     let uu____23279 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23294 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23279,
                                       uu____23294) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23268 in
                                 let uu____23309 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23267,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23309) in
                               FStar_SMTEncoding_Util.mkAssume uu____23260 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23312 =
            let uu____23325 =
              let uu____23326 = FStar_Syntax_Subst.compress k in
              uu____23326.FStar_Syntax_Syntax.n in
            match uu____23325 with
            | FStar_Syntax_Syntax.Tm_arrow (formals, kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23371 -> (tps, k) in
          (match uu____23312 with
           | (formals, res) ->
               let uu____23394 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23394 with
                | (formals1, res1) ->
                    let uu____23405 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23405 with
                     | (vars, guards, env', binder_decls, uu____23430) ->
                         let arity = FStar_List.length vars in
                         let uu____23444 =
                           new_term_constant_and_tok_from_lid env t arity in
                         (match uu____23444 with
                          | (tname, ttok, env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23467 =
                                  let uu____23474 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23474) in
                                FStar_SMTEncoding_Util.mkApp uu____23467 in
                              let uu____23483 =
                                let tname_decl =
                                  let uu____23493 =
                                    let uu____23494 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23526 ->
                                              match uu____23526 with
                                              | (n1, s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23539 = varops.next_id () in
                                    (tname, uu____23494,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23539, false) in
                                  constructor_or_logic_type_decl uu____23493 in
                                let uu____23548 =
                                  match vars with
                                  | [] ->
                                      let uu____23561 =
                                        let uu____23562 =
                                          let uu____23565 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_43 ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23565 in
                                        push_free_var env1 t arity tname
                                          uu____23562 in
                                      ([], uu____23561)
                                  | uu____23576 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23585 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23585 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23599 =
                                          let uu____23606 =
                                            let uu____23607 =
                                              let uu____23622 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23622) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23607 in
                                          (uu____23606,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23599 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23548 with
                                | (tok_decls, env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23483 with
                               | (decls, env2) ->
                                   let kindingAx =
                                     let uu____23662 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23662 with
                                     | (k1, decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23680 =
                                               let uu____23681 =
                                                 let uu____23688 =
                                                   let uu____23689 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23689 in
                                                 (uu____23688,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23681 in
                                             [uu____23680]
                                           else [] in
                                         let uu____23693 =
                                           let uu____23696 =
                                             let uu____23699 =
                                               let uu____23700 =
                                                 let uu____23707 =
                                                   let uu____23708 =
                                                     let uu____23719 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23719) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23708 in
                                                 (uu____23707,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23700 in
                                             [uu____23699] in
                                           FStar_List.append karr uu____23696 in
                                         FStar_List.append decls1 uu____23693 in
                                   let aux =
                                     let uu____23735 =
                                       let uu____23738 =
                                         inversion_axioms tapp vars in
                                       let uu____23741 =
                                         let uu____23744 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23744] in
                                       FStar_List.append uu____23738
                                         uu____23741 in
                                     FStar_List.append kindingAx uu____23735 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d, uu____23751, uu____23752, uu____23753, uu____23754,
           uu____23755)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d, uu____23763, t, uu____23765, n_tps, uu____23767) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____23775 = FStar_Syntax_Util.arrow_formals t in
          (match uu____23775 with
           | (formals, t_res) ->
               let arity = FStar_List.length formals in
               let uu____23815 =
                 new_term_constant_and_tok_from_lid env d arity in
               (match uu____23815 with
                | (ddconstrsym, ddtok, env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
                    let uu____23836 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____23836 with
                     | (fuel_var, fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____23850 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____23850 with
                          | (vars, guards, env', binder_decls, names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1 ->
                                        fun x ->
                                          let projectible = true in
                                          let uu____23920 =
                                            mk_term_projector_name d x in
                                          (uu____23920,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____23922 =
                                  let uu____23941 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23941, true) in
                                FStar_All.pipe_right uu____23922
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____23980 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____23980 with
                               | (tok_typing, decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23992::uu____23993 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____24038 =
                                           let uu____24049 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24049) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24038
                                     | uu____24074 -> tok_typing in
                                   let uu____24083 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24083 with
                                    | (vars', guards', env'', decls_formals,
                                       uu____24108) ->
                                        let uu____24121 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____24121 with
                                         | (ty_pred', decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24152 ->
                                                   let uu____24159 =
                                                     let uu____24160 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24160 in
                                                   [uu____24159] in
                                             let encode_elim uu____24170 =
                                               let uu____24171 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24171 with
                                               | (head1, args) ->
                                                   let uu____24214 =
                                                     let uu____24215 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24215.FStar_Syntax_Syntax.n in
                                                   (match uu____24214 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24225;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24226;_},
                                                         uu____24227)
                                                        ->
                                                        let uu____24232 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        (match uu____24232
                                                         with
                                                         | (encoded_head,
                                                            encoded_head_arity)
                                                             ->
                                                             let uu____24245
                                                               =
                                                               encode_args
                                                                 args env' in
                                                             (match uu____24245
                                                              with
                                                              | (encoded_args,
                                                                 arg_decls)
                                                                  ->
                                                                  let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____24288
                                                                    ->
                                                                    let uu____24289
                                                                    =
                                                                    let uu____24294
                                                                    =
                                                                    let uu____24295
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24295 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24294) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24289
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____24311
                                                                    =
                                                                    let uu____24312
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24312 in
                                                                    if
                                                                    uu____24311
                                                                    then
                                                                    let uu____24325
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24325]
                                                                    else [])) in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1 in
                                                                  let uu____24327
                                                                    =
                                                                    let uu____24340
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24390
                                                                    ->
                                                                    fun
                                                                    uu____24391
                                                                    ->
                                                                    match 
                                                                    (uu____24390,
                                                                    uu____24391)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____24486
                                                                    =
                                                                    let uu____24493
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24493 in
                                                                    (match uu____24486
                                                                    with
                                                                    | 
                                                                    (uu____24506,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24514
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24514
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24516
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24516
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____24340 in
                                                                  (match uu____24327
                                                                   with
                                                                   | 
                                                                   (uu____24531,
                                                                    arg_vars,
                                                                    elim_eqns_or_guards,
                                                                    uu____24534)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                    let ty =
                                                                    maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1 in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____24562
                                                                    =
                                                                    let uu____24569
                                                                    =
                                                                    let uu____24570
                                                                    =
                                                                    let uu____24581
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24592
                                                                    =
                                                                    let uu____24593
                                                                    =
                                                                    let uu____24598
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24598) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24593 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24581,
                                                                    uu____24592) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24570 in
                                                                    (uu____24569,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24562 in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24621
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24621,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24623
                                                                    =
                                                                    let uu____24630
                                                                    =
                                                                    let uu____24631
                                                                    =
                                                                    let uu____24642
                                                                    =
                                                                    let uu____24647
                                                                    =
                                                                    let uu____24650
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24650] in
                                                                    [uu____24647] in
                                                                    let uu____24655
                                                                    =
                                                                    let uu____24656
                                                                    =
                                                                    let uu____24661
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24661,
                                                                    uu____24662) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24656 in
                                                                    (uu____24642,
                                                                    [x],
                                                                    uu____24655) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24631 in
                                                                    let uu____24681
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24630,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24681) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24623
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24688
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v1 ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____24716
                                                                    =
                                                                    let uu____24717
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24717
                                                                    dapp1 in
                                                                    [uu____24716]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24688
                                                                    FStar_List.flatten in
                                                                    let uu____24724
                                                                    =
                                                                    let uu____24731
                                                                    =
                                                                    let uu____24732
                                                                    =
                                                                    let uu____24743
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24754
                                                                    =
                                                                    let uu____24755
                                                                    =
                                                                    let uu____24760
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24760) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24755 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24743,
                                                                    uu____24754) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24732 in
                                                                    (uu____24731,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24724) in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____24780 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        (match uu____24780
                                                         with
                                                         | (encoded_head,
                                                            encoded_head_arity)
                                                             ->
                                                             let uu____24793
                                                               =
                                                               encode_args
                                                                 args env' in
                                                             (match uu____24793
                                                              with
                                                              | (encoded_args,
                                                                 arg_decls)
                                                                  ->
                                                                  let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____24836
                                                                    ->
                                                                    let uu____24837
                                                                    =
                                                                    let uu____24842
                                                                    =
                                                                    let uu____24843
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24843 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24842) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24837
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____24859
                                                                    =
                                                                    let uu____24860
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24860 in
                                                                    if
                                                                    uu____24859
                                                                    then
                                                                    let uu____24873
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24873]
                                                                    else [])) in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1 in
                                                                  let uu____24875
                                                                    =
                                                                    let uu____24888
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24938
                                                                    ->
                                                                    fun
                                                                    uu____24939
                                                                    ->
                                                                    match 
                                                                    (uu____24938,
                                                                    uu____24939)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____25034
                                                                    =
                                                                    let uu____25041
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25041 in
                                                                    (match uu____25034
                                                                    with
                                                                    | 
                                                                    (uu____25054,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25062
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25062
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25064
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25064
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____24888 in
                                                                  (match uu____24875
                                                                   with
                                                                   | 
                                                                   (uu____25079,
                                                                    arg_vars,
                                                                    elim_eqns_or_guards,
                                                                    uu____25082)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                    let ty =
                                                                    maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1 in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____25110
                                                                    =
                                                                    let uu____25117
                                                                    =
                                                                    let uu____25118
                                                                    =
                                                                    let uu____25129
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25140
                                                                    =
                                                                    let uu____25141
                                                                    =
                                                                    let uu____25146
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25146) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25141 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25129,
                                                                    uu____25140) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25118 in
                                                                    (uu____25117,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25110 in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25169
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25169,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25171
                                                                    =
                                                                    let uu____25178
                                                                    =
                                                                    let uu____25179
                                                                    =
                                                                    let uu____25190
                                                                    =
                                                                    let uu____25195
                                                                    =
                                                                    let uu____25198
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25198] in
                                                                    [uu____25195] in
                                                                    let uu____25203
                                                                    =
                                                                    let uu____25204
                                                                    =
                                                                    let uu____25209
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25210
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25209,
                                                                    uu____25210) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25204 in
                                                                    (uu____25190,
                                                                    [x],
                                                                    uu____25203) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25179 in
                                                                    let uu____25229
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25178,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25229) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25171
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25236
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v1 ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25264
                                                                    =
                                                                    let uu____25265
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25265
                                                                    dapp1 in
                                                                    [uu____25264]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25236
                                                                    FStar_List.flatten in
                                                                    let uu____25272
                                                                    =
                                                                    let uu____25279
                                                                    =
                                                                    let uu____25280
                                                                    =
                                                                    let uu____25291
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25302
                                                                    =
                                                                    let uu____25303
                                                                    =
                                                                    let uu____25308
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25308) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25303 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25291,
                                                                    uu____25302) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25280 in
                                                                    (uu____25279,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25272) in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____25327 ->
                                                        ((let uu____25329 =
                                                            let uu____25334 =
                                                              let uu____25335
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25336
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25335
                                                                uu____25336 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25334) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25329);
                                                         ([], []))) in
                                             let uu____25341 = encode_elim () in
                                             (match uu____25341 with
                                              | (decls2, elim) ->
                                                  let g =
                                                    let uu____25361 =
                                                      let uu____25364 =
                                                        let uu____25367 =
                                                          let uu____25370 =
                                                            let uu____25373 =
                                                              let uu____25374
                                                                =
                                                                let uu____25385
                                                                  =
                                                                  let uu____25388
                                                                    =
                                                                    let uu____25389
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25389 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25388 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25385) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25374 in
                                                            [uu____25373] in
                                                          let uu____25394 =
                                                            let uu____25397 =
                                                              let uu____25400
                                                                =
                                                                let uu____25403
                                                                  =
                                                                  let uu____25406
                                                                    =
                                                                    let uu____25409
                                                                    =
                                                                    let uu____25412
                                                                    =
                                                                    let uu____25413
                                                                    =
                                                                    let uu____25420
                                                                    =
                                                                    let uu____25421
                                                                    =
                                                                    let uu____25432
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25432) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25421 in
                                                                    (uu____25420,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25413 in
                                                                    let uu____25445
                                                                    =
                                                                    let uu____25448
                                                                    =
                                                                    let uu____25449
                                                                    =
                                                                    let uu____25456
                                                                    =
                                                                    let uu____25457
                                                                    =
                                                                    let uu____25468
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25479
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25468,
                                                                    uu____25479) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25457 in
                                                                    (uu____25456,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25449 in
                                                                    [uu____25448] in
                                                                    uu____25412
                                                                    ::
                                                                    uu____25445 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25409 in
                                                                  FStar_List.append
                                                                    uu____25406
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25403 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25400 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25397 in
                                                          FStar_List.append
                                                            uu____25370
                                                            uu____25394 in
                                                        FStar_List.append
                                                          decls3 uu____25367 in
                                                      FStar_List.append
                                                        decls2 uu____25364 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25361 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and (encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list, env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun ses ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____25525 ->
              fun se ->
                match uu____25525 with
                | (g, env1) ->
                    let uu____25545 = encode_sigelt env1 se in
                    (match uu____25545 with
                     | (g', env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t, env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bindings ->
      let encode_binding b uu____25602 =
        match uu____25602 with
        | (i, decls, env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25634 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____25640 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25640
                   then
                     let uu____25641 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25642 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25643 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25641 uu____25642 uu____25643
                   else ());
                  (let uu____25645 = encode_term t1 env1 in
                   match uu____25645 with
                   | (t, decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25661 =
                         let uu____25668 =
                           let uu____25669 =
                             let uu____25670 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25670
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25669 in
                         new_term_constant_from_string env1 x uu____25668 in
                       (match uu____25661 with
                        | (xxsym, xx, env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25686 = FStar_Options.log_queries () in
                              if uu____25686
                              then
                                let uu____25689 =
                                  let uu____25690 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25691 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25692 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25690 uu____25691 uu____25692 in
                                FStar_Pervasives_Native.Some uu____25689
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x, (uu____25708, t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25722 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25722 with
                  | (g, env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25745, se, uu____25747) ->
                 let uu____25752 = encode_sigelt env1 se in
                 (match uu____25752 with
                  | (g, env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25769, se) ->
                 let uu____25775 = encode_sigelt env1 se in
                 (match uu____25775 with
                  | (g, env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____25792 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____25792 with | (uu____25815, decls, env1) -> (decls, env1)
let encode_labels :
  'Auu____25827 'Auu____25828 .
    ((Prims.string, FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,
      'Auu____25827, 'Auu____25828) FStar_Pervasives_Native.tuple3 Prims.list
      ->
      (FStar_SMTEncoding_Term.decl Prims.list,
        FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25896 ->
              match uu____25896 with
              | (l, uu____25908, uu____25909) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____25955 ->
              match uu____25955 with
              | (l, uu____25969, uu____25970) ->
                  let uu____25979 =
                    FStar_All.pipe_left
                      (fun _0_44 -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____25980 =
                    let uu____25983 =
                      let uu____25984 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____25984 in
                    [uu____25983] in
                  uu____25979 :: uu____25980)) in
    (prefix1, suffix)
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv ->
    let uu____26033 =
      let uu____26036 =
        let uu____26037 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26040 =
          let uu____26041 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26041 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26037;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26040
        } in
      [uu____26036] in
    FStar_ST.op_Colon_Equals last_env uu____26033
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn ->
    fun tcenv ->
      let uu____26077 = FStar_ST.op_Bang last_env in
      match uu____26077 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26110 ->
          let uu___134_26113 = e in
          let uu____26114 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___134_26113.bindings);
            depth = (uu___134_26113.depth);
            tcenv;
            warn = (uu___134_26113.warn);
            cache = (uu___134_26113.cache);
            nolabels = (uu___134_26113.nolabels);
            use_zfuel_name = (uu___134_26113.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_26113.encode_non_total_function_typ);
            current_module_name = uu____26114
          }
let (set_env : env_t -> Prims.unit) =
  fun env ->
    let uu____26118 = FStar_ST.op_Bang last_env in
    match uu____26118 with
    | [] -> failwith "Empty env stack"
    | uu____26150::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____26185 ->
    let uu____26186 = FStar_ST.op_Bang last_env in
    match uu____26186 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___135_26226 = hd1 in
          {
            bindings = (uu___135_26226.bindings);
            depth = (uu___135_26226.depth);
            tcenv = (uu___135_26226.tcenv);
            warn = (uu___135_26226.warn);
            cache = refs;
            nolabels = (uu___135_26226.nolabels);
            use_zfuel_name = (uu___135_26226.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___135_26226.encode_non_total_function_typ);
            current_module_name = (uu___135_26226.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____26258 ->
    let uu____26259 = FStar_ST.op_Bang last_env in
    match uu____26259 with
    | [] -> failwith "Popping an empty stack"
    | uu____26291::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let (init : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let (push : Prims.string -> Prims.unit) =
  fun msg -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let (pop : Prims.string -> Prims.unit) =
  fun msg -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let (open_fact_db_tags :
  env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list) = fun env -> []
let (place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun fact_db_ids ->
      fun d ->
        match (fact_db_ids, d) with
        | (uu____26361::uu____26362, FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___136_26370 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___136_26370.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___136_26370.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___136_26370.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26371 -> d
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env ->
    fun lid ->
      let uu____26386 =
        let uu____26389 =
          let uu____26390 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26390 in
        let uu____26391 = open_fact_db_tags env in uu____26389 :: uu____26391 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26386
let (encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list, env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____26413 = encode_sigelt env se in
      match uu____26413 with
      | (g, env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun tcenv ->
    fun se ->
      let caption decls =
        let uu____26449 = FStar_Options.log_queries () in
        if uu____26449
        then
          let uu____26452 =
            let uu____26453 =
              let uu____26454 =
                let uu____26455 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26455 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26454 in
            FStar_SMTEncoding_Term.Caption uu____26453 in
          uu____26452 :: decls
        else decls in
      (let uu____26466 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26466
       then
         let uu____26467 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26467
       else ());
      (let env =
         let uu____26470 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26470 tcenv in
       let uu____26471 = encode_top_level_facts env se in
       match uu____26471 with
       | (decls, env1) ->
           (set_env env1;
            (let uu____26485 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26485)))
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun tcenv ->
    fun modul ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26497 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26497
       then
         let uu____26498 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26498
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26533 ->
                 fun se ->
                   match uu____26533 with
                   | (g, env2) ->
                       let uu____26553 = encode_top_level_facts env2 se in
                       (match uu____26553 with
                        | (g', env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26576 =
         encode_signature
           (let uu___137_26585 = env in
            {
              bindings = (uu___137_26585.bindings);
              depth = (uu___137_26585.depth);
              tcenv = (uu___137_26585.tcenv);
              warn = false;
              cache = (uu___137_26585.cache);
              nolabels = (uu___137_26585.nolabels);
              use_zfuel_name = (uu___137_26585.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___137_26585.encode_non_total_function_typ);
              current_module_name = (uu___137_26585.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26576 with
       | (decls, env1) ->
           let caption decls1 =
             let uu____26602 = FStar_Options.log_queries () in
             if uu____26602
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___138_26610 = env1 in
               {
                 bindings = (uu___138_26610.bindings);
                 depth = (uu___138_26610.depth);
                 tcenv = (uu___138_26610.tcenv);
                 warn = true;
                 cache = (uu___138_26610.cache);
                 nolabels = (uu___138_26610.nolabels);
                 use_zfuel_name = (uu___138_26610.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___138_26610.encode_non_total_function_typ);
                 current_module_name = (uu___138_26610.current_module_name)
               });
            (let uu____26612 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26612
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let (encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,
          FStar_SMTEncoding_ErrorReporting.label Prims.list,
          FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____26664 =
           let uu____26665 = FStar_TypeChecker_Env.current_module tcenv in
           uu____26665.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26664);
        (let env =
           let uu____26667 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____26667 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv (fun bs -> fun b -> b :: bs)
             [] in
         let uu____26679 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26714 = aux rest in
                 (match uu____26714 with
                  | (out, rest1) ->
                      let t =
                        let uu____26744 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____26744 with
                        | FStar_Pervasives_Native.Some uu____26749 ->
                            let uu____26750 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____26750
                              x.FStar_Syntax_Syntax.sort
                        | uu____26751 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____26755 =
                        let uu____26758 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___139_26761 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___139_26761.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___139_26761.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____26758 :: out in
                      (uu____26755, rest1))
             | uu____26766 -> ([], bindings1) in
           let uu____26773 = aux bindings in
           match uu____26773 with
           | (closing, bindings1) ->
               let uu____26798 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____26798, bindings1) in
         match uu____26679 with
         | (q1, bindings1) ->
             let uu____26821 =
               let uu____26826 =
                 FStar_List.filter
                   (fun uu___104_26831 ->
                      match uu___104_26831 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26832 ->
                          false
                      | uu____26839 -> true) bindings1 in
               encode_env_bindings env uu____26826 in
             (match uu____26821 with
              | (env_decls, env1) ->
                  ((let uu____26857 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____26857
                    then
                      let uu____26858 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26858
                    else ());
                   (let uu____26860 = encode_formula q1 env1 in
                    match uu____26860 with
                    | (phi, qdecls) ->
                        let uu____26881 =
                          let uu____26886 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26886 phi in
                        (match uu____26881 with
                         | (labels, phi1) ->
                             let uu____26903 = encode_labels labels in
                             (match uu____26903 with
                              | (label_prefix, label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____26940 =
                                      let uu____26947 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____26948 =
                                        varops.mk_unique "@query" in
                                      (uu____26947,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26948) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26940 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))