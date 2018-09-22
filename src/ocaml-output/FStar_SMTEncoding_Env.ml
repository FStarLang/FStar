open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____6 -> false
  
let add_fuel :
  'Auu____13 . 'Auu____13 -> 'Auu____13 Prims.list -> 'Auu____13 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____30 = FStar_Options.unthrottle_inductives ()  in
      if uu____30 then tl1 else x :: tl1
  
let withenv :
  'Auu____44 'Auu____45 'Auu____46 .
    'Auu____44 ->
      ('Auu____45,'Auu____46) FStar_Pervasives_Native.tuple2 ->
        ('Auu____45,'Auu____46,'Auu____44) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____66  -> match uu____66 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____81 'Auu____82 'Auu____83 .
    (('Auu____81,'Auu____82) FStar_Util.either,'Auu____83)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____81,'Auu____82) FStar_Util.either,'Auu____83)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___265_130  ->
         match uu___265_130 with
         | (FStar_Util.Inl uu____139,uu____140) -> false
         | uu____145 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____171 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____171
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____192 =
          let uu____193 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____193  in
        let uu____194 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____194 with
        | (uu____199,t) ->
            let uu____201 =
              let uu____202 = FStar_Syntax_Subst.compress t  in
              uu____202.FStar_Syntax_Syntax.n  in
            (match uu____201 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____227 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____227 with
                  | (binders,uu____233) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____256 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____267 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____267
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____278 =
        let uu____283 = mk_term_projector_name lid a  in
        (uu____283,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____278
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____294 =
        let uu____299 = mk_term_projector_name_by_pos lid i  in
        (uu____299,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____294
  
let mk_data_tester :
  'Auu____308 .
    'Auu____308 ->
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
  snapshot: unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2 ;
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
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__pop
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__snapshot
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__rollback
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1081 =
    let uu____1082 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1085 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1082, uu____1085)  in
  let scopes =
    let uu____1105 = let uu____1116 = new_scope ()  in [uu____1116]  in
    FStar_Util.mk_ref uu____1105  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1159 =
        let uu____1162 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1162
          (fun uu____1245  ->
             match uu____1245 with
             | (names1,uu____1257) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1159 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1266 ->
          (FStar_Util.incr ctr;
           (let uu____1301 =
              let uu____1302 =
                let uu____1303 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1303  in
              Prims.strcat "__" uu____1302  in
            Prims.strcat y1 uu____1301))
       in
    let top_scope =
      let uu____1348 =
        let uu____1357 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1357
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1348  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1474 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1556 =
      let uu____1557 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1557  in
    FStar_Util.format2 "%s_%s" pfx uu____1556  in
  let string_const s =
    let uu____1564 =
      let uu____1567 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1567
        (fun uu____1650  ->
           match uu____1650 with
           | (uu____1661,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1564 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1674 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1674  in
        let top_scope =
          let uu____1678 =
            let uu____1687 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1687  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1678  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1787 =
    let uu____1788 =
      let uu____1799 = new_scope ()  in
      let uu____1808 = FStar_ST.op_Bang scopes  in uu____1799 :: uu____1808
       in
    FStar_ST.op_Colon_Equals scopes uu____1788  in
  let pop1 uu____1954 =
    let uu____1955 =
      let uu____1966 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1966
       in
    FStar_ST.op_Colon_Equals scopes uu____1955  in
  let snapshot1 uu____2116 = FStar_Common.snapshot push1 scopes ()  in
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
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option }
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__fvar_lid
  
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_arity
  
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_id
  
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_token
  
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_fuel_partial_app
  
let binder_of_eithervar :
  'Auu____2300 'Auu____2301 .
    'Auu____2300 ->
      ('Auu____2300,'Auu____2301 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
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
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
  
type env_t =
  {
  bvar_bindings:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2 FStar_Util.pimap FStar_Util.psmap
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
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2 FStar_Util.pimap FStar_Util.psmap)
  =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__bvar_bindings
  
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> fvar_binding FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__fvar_bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__warn
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__cache
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__current_module_name
  
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__encoding_quantifier
  
let mk_cache_entry :
  'Auu____2822 .
    'Auu____2822 ->
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
                 (fun uu___266_2860  ->
                    match uu___266_2860 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2864 -> []))
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
                    fun uu____2915  ->
                      fun acc1  ->
                        match uu____2915 with
                        | (x,_term) ->
                            let uu____2927 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____2927 :: acc1) acc) []
       in
    let allvars =
      FStar_Util.psmap_fold e.fvar_bindings
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____2943 ->
          let uu____2946 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____2946
       in
    FStar_String.concat ", " (last_fvar :: bvars)
  
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      let uu____2963 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____2963 with
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
  'Auu____3029 .
    (FStar_Syntax_Syntax.bv,'Auu____3029) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____3029) FStar_Pervasives_Native.tuple2
        FStar_Util.pimap FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv,'Auu____3029) FStar_Pervasives_Native.tuple2
          FStar_Util.pimap FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3089 =
             let uu____3096 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3096 pimap_opt  in
           FStar_Util.pimap_add uu____3089
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
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____3148 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____3148)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      let uu____3167 =
        let uu___267_3168 = env  in
        let uu____3169 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3169;
          fvar_bindings = (uu___267_3168.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___267_3168.tcenv);
          warn = (uu___267_3168.warn);
          cache = (uu___267_3168.cache);
          nolabels = (uu___267_3168.nolabels);
          use_zfuel_name = (uu___267_3168.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___267_3168.encode_non_total_function_typ);
          current_module_name = (uu___267_3168.current_module_name);
          encoding_quantifier = (uu___267_3168.encoding_quantifier)
        }  in
      (ysym, y, uu____3167)
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      let uu____3198 =
        let uu___268_3199 = env  in
        let uu____3200 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3200;
          fvar_bindings = (uu___268_3199.fvar_bindings);
          depth = (uu___268_3199.depth);
          tcenv = (uu___268_3199.tcenv);
          warn = (uu___268_3199.warn);
          cache = (uu___268_3199.cache);
          nolabels = (uu___268_3199.nolabels);
          use_zfuel_name = (uu___268_3199.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___268_3199.encode_non_total_function_typ);
          current_module_name = (uu___268_3199.current_module_name);
          encoding_quantifier = (uu___268_3199.encoding_quantifier)
        }  in
      (ysym, y, uu____3198)
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        let uu____3234 =
          let uu___269_3235 = env  in
          let uu____3236 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3236;
            fvar_bindings = (uu___269_3235.fvar_bindings);
            depth = (uu___269_3235.depth);
            tcenv = (uu___269_3235.tcenv);
            warn = (uu___269_3235.warn);
            cache = (uu___269_3235.cache);
            nolabels = (uu___269_3235.nolabels);
            use_zfuel_name = (uu___269_3235.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___269_3235.encode_non_total_function_typ);
            current_module_name = (uu___269_3235.current_module_name);
            encoding_quantifier = (uu___269_3235.encoding_quantifier)
          }  in
        (ysym, y, uu____3234)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___270_3260 = env  in
        let uu____3261 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3261;
          fvar_bindings = (uu___270_3260.fvar_bindings);
          depth = (uu___270_3260.depth);
          tcenv = (uu___270_3260.tcenv);
          warn = (uu___270_3260.warn);
          cache = (uu___270_3260.cache);
          nolabels = (uu___270_3260.nolabels);
          use_zfuel_name = (uu___270_3260.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___270_3260.encode_non_total_function_typ);
          current_module_name = (uu___270_3260.current_module_name);
          encoding_quantifier = (uu___270_3260.encoding_quantifier)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3280 = lookup_bvar_binding env a  in
      match uu____3280 with
      | FStar_Pervasives_Native.None  ->
          let uu____3291 = lookup_bvar_binding env a  in
          (match uu____3291 with
           | FStar_Pervasives_Native.None  ->
               let uu____3302 =
                 let uu____3303 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3304 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3303 uu____3304
                  in
               failwith uu____3302
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            fvar_binding)
  =
  fun lid  ->
    fun fname  ->
      fun arity  ->
        fun ftok  ->
          fun fuel_partial_app  ->
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
        (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let fname = varops.new_fvar x  in
        let ftok_name = Prims.strcat fname "@tok"  in
        let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
        let fvb =
          mk_fvb x fname arity (FStar_Pervasives_Native.Some ftok)
            FStar_Pervasives_Native.None
           in
        let uu____3377 =
          let uu___271_3378 = env  in
          let uu____3379 = add_fvar_binding fvb env.fvar_bindings  in
          {
            bvar_bindings = (uu___271_3378.bvar_bindings);
            fvar_bindings = uu____3379;
            depth = (uu___271_3378.depth);
            tcenv = (uu___271_3378.tcenv);
            warn = (uu___271_3378.warn);
            cache = (uu___271_3378.cache);
            nolabels = (uu___271_3378.nolabels);
            use_zfuel_name = (uu___271_3378.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___271_3378.encode_non_total_function_typ);
            current_module_name = (uu___271_3378.current_module_name);
            encoding_quantifier = (uu___271_3378.encoding_quantifier)
          }  in
        (fname, ftok_name, uu____3377)
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____3392 = lookup_fvar_binding env a  in
      match uu____3392 with
      | FStar_Pervasives_Native.None  ->
          let uu____3395 =
            let uu____3396 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3396  in
          failwith uu____3395
      | FStar_Pervasives_Native.Some s -> s
  
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
            let fvb = mk_fvb x fname arity ftok FStar_Pervasives_Native.None
               in
            let uu___272_3428 = env  in
            let uu____3429 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___272_3428.bvar_bindings);
              fvar_bindings = uu____3429;
              depth = (uu___272_3428.depth);
              tcenv = (uu___272_3428.tcenv);
              warn = (uu___272_3428.warn);
              cache = (uu___272_3428.cache);
              nolabels = (uu___272_3428.nolabels);
              use_zfuel_name = (uu___272_3428.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___272_3428.encode_non_total_function_typ);
              current_module_name = (uu___272_3428.current_module_name);
              encoding_quantifier = (uu___272_3428.encoding_quantifier)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____3449 =
            let uu____3456 =
              let uu____3459 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____3459]  in
            (f, uu____3456)  in
          FStar_SMTEncoding_Util.mkApp uu____3449  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___273_3465 = env  in
        let uu____3466 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___273_3465.bvar_bindings);
          fvar_bindings = uu____3466;
          depth = (uu___273_3465.depth);
          tcenv = (uu___273_3465.tcenv);
          warn = (uu___273_3465.warn);
          cache = (uu___273_3465.cache);
          nolabels = (uu___273_3465.nolabels);
          use_zfuel_name = (uu___273_3465.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___273_3465.encode_non_total_function_typ);
          current_module_name = (uu___273_3465.current_module_name);
          encoding_quantifier = (uu___273_3465.encoding_quantifier)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____3481 = lookup_fvar_binding env l  in
      match uu____3481 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3490 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3498,fuel::[]) ->
                         let uu____3502 =
                           let uu____3503 =
                             let uu____3504 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____3504
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____3503 "fuel"  in
                         if uu____3502
                         then
                           let uu____3515 =
                             let uu____3516 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3516
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_16  ->
                                FStar_Pervasives_Native.Some _0_16)
                             uu____3515
                         else FStar_Pervasives_Native.Some t
                     | uu____3520 -> FStar_Pervasives_Native.Some t)
                | uu____3521 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____3538 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3538 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3542 =
            let uu____3543 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3543  in
          failwith uu____3542
  
let (lookup_free_var_name :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      ((fvb.smt_id), (fvb.smt_arity))
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list,
        Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____3596;
            FStar_SMTEncoding_Term.rng = uu____3597;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____3612 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____3640 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.psmap_find_map env.fvar_bindings
        (fun uu____3657  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  