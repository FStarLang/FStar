open Prims
exception Inner_let_rec 
let uu___is_Inner_let_rec : Prims.exn -> Prims.bool =
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
      (fun uu___55_130  ->
         match uu___55_130 with
         | (FStar_Util.Inl uu____139,uu____140) -> false
         | uu____145 -> true) args
  
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___57_172 = a  in
        let uu____173 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____173;
          FStar_Syntax_Syntax.index = (uu___57_172.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___57_172.FStar_Syntax_Syntax.sort)
        }  in
      let uu____174 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____174
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____195 =
          let uu____196 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____196  in
        let uu____197 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____197 with
        | (uu____202,t) ->
            let uu____204 =
              let uu____205 = FStar_Syntax_Subst.compress t  in
              uu____205.FStar_Syntax_Syntax.n  in
            (match uu____204 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____226 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____226 with
                  | (binders,uu____232) ->
                      if
                        (i < (Prims.lift_native_int (0))) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____247 -> fail1 ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____258 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____258
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____269 =
        let uu____274 = mk_term_projector_name lid a  in
        (uu____274,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____269
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____285 =
        let uu____290 = mk_term_projector_name_by_pos lid i  in
        (uu____290,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____285
  
let mk_data_tester :
  'Auu____299 .
    'Auu____299 ->
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
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }[@@deriving show]
let __proj__Mkvarops_t__item__push : varops_t -> unit -> unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let __proj__Mkvarops_t__item__pop : varops_t -> unit -> unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
  
let __proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
  
let __proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
  
let __proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
  
let __proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
  
let __proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
  
let __proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
  
let varops : varops_t =
  let initial_ctr = (Prims.lift_native_int (100))  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____800 =
    let uu____801 = FStar_Util.smap_create (Prims.lift_native_int (100))  in
    let uu____804 = FStar_Util.smap_create (Prims.lift_native_int (100))  in
    (uu____801, uu____804)  in
  let scopes =
    let uu____824 = let uu____835 = new_scope ()  in [uu____835]  in
    FStar_Util.mk_ref uu____824  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____878 =
        let uu____881 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____881
          (fun uu____968  ->
             match uu____968 with
             | (names1,uu____980) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____878 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____989 ->
          (FStar_Util.incr ctr;
           (let uu____1024 =
              let uu____1025 =
                let uu____1026 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1026  in
              Prims.strcat "__" uu____1025  in
            Prims.strcat y1 uu____1024))
       in
    let top_scope =
      let uu____1075 =
        let uu____1084 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1084
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1075  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1205 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1291 =
      let uu____1292 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1292  in
    FStar_Util.format2 "%s_%s" pfx uu____1291  in
  let string_const s =
    let uu____1299 =
      let uu____1302 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1302
        (fun uu____1389  ->
           match uu____1389 with
           | (uu____1400,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1299 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1413 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1413  in
        let top_scope =
          let uu____1417 =
            let uu____1426 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1426  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1417  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1530 =
    let uu____1531 =
      let uu____1542 = new_scope ()  in
      let uu____1551 = FStar_ST.op_Bang scopes  in uu____1542 :: uu____1551
       in
    FStar_ST.op_Colon_Equals scopes uu____1531  in
  let pop1 uu____1705 =
    let uu____1706 =
      let uu____1717 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1717
       in
    FStar_ST.op_Colon_Equals scopes uu____1706  in
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
let unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___58_1871 = x  in
    let uu____1872 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1872;
      FStar_Syntax_Syntax.index = (uu___58_1871.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___58_1871.FStar_Syntax_Syntax.sort)
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
let __proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__fvar_lid
  
let __proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_arity
  
let __proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_id
  
let __proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_token
  
let __proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_fuel_partial_app
  
let binder_of_eithervar :
  'Auu____1986 'Auu____1987 .
    'Auu____1986 ->
      ('Auu____1986,'Auu____1987 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
let __proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let __proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let __proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list =
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
  current_module_name: Prims.string }[@@deriving show]
let __proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2 FStar_Util.pimap FStar_Util.psmap
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
        current_module_name = __fname__current_module_name;_} ->
        __fname__bvar_bindings
  
let __proj__Mkenv_t__item__fvar_bindings :
  env_t -> fvar_binding FStar_Util.psmap =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__fvar_bindings
  
let __proj__Mkenv_t__item__depth : env_t -> Prims.int =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
  
let __proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
  
let __proj__Mkenv_t__item__warn : env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
  
let __proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
  
let __proj__Mkenv_t__item__nolabels : env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
  
let __proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
  
let __proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
  
let __proj__Mkenv_t__item__current_module_name : env_t -> Prims.string =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
  
let mk_cache_entry :
  'Auu____2465 .
    'Auu____2465 ->
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
                 (fun uu___56_2503  ->
                    match uu___56_2503 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2507 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls1;
            cache_symbol_assumption_names = names1
          }
  
let use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let print_env : env_t -> Prims.string =
  fun e  ->
    let bvars =
      FStar_Util.psmap_fold e.bvar_bindings
        (fun _k  ->
           fun pi  ->
             fun acc  ->
               FStar_Util.pimap_fold pi
                 (fun _i  ->
                    fun uu____2558  ->
                      fun acc1  ->
                        match uu____2558 with
                        | (x,_term) ->
                            let uu____2570 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____2570 :: acc1) acc) []
       in
    let allvars =
      FStar_Util.psmap_fold e.fvar_bindings
        (fun _k  ->
           fun fvb  ->
             fun acc  ->
               let uu____2585 = FStar_Syntax_Print.lid_to_string fvb.fvar_lid
                  in
               uu____2585 :: acc) bvars
       in
    FStar_String.concat ", " allvars
  
let lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      let uu____2602 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____2602 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      FStar_Util.psmap_try_find env.fvar_bindings lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____2668 .
    (FStar_Syntax_Syntax.bv,'Auu____2668) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____2668) FStar_Pervasives_Native.tuple2
        FStar_Util.pimap FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv,'Auu____2668) FStar_Pervasives_Native.tuple2
          FStar_Util.pimap FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____2728 =
             let uu____2735 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____2735 pimap_opt  in
           FStar_Util.pimap_add uu____2728
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let add_fvar_binding :
  fvar_binding ->
    fvar_binding FStar_Util.psmap -> fvar_binding FStar_Util.psmap
  =
  fun fvb  ->
    fun fvbs  -> FStar_Util.psmap_add fvbs (fvb.fvar_lid).FStar_Ident.str fvb
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2787 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2787)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      let uu____2806 =
        let uu___59_2807 = env  in
        let uu____2808 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____2808;
          fvar_bindings = (uu___59_2807.fvar_bindings);
          depth = (env.depth + (Prims.lift_native_int (1)));
          tcenv = (uu___59_2807.tcenv);
          warn = (uu___59_2807.warn);
          cache = (uu___59_2807.cache);
          nolabels = (uu___59_2807.nolabels);
          use_zfuel_name = (uu___59_2807.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___59_2807.encode_non_total_function_typ);
          current_module_name = (uu___59_2807.current_module_name)
        }  in
      (ysym, y, uu____2806)
  
let new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      let uu____2837 =
        let uu___60_2838 = env  in
        let uu____2839 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____2839;
          fvar_bindings = (uu___60_2838.fvar_bindings);
          depth = (uu___60_2838.depth);
          tcenv = (uu___60_2838.tcenv);
          warn = (uu___60_2838.warn);
          cache = (uu___60_2838.cache);
          nolabels = (uu___60_2838.nolabels);
          use_zfuel_name = (uu___60_2838.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___60_2838.encode_non_total_function_typ);
          current_module_name = (uu___60_2838.current_module_name)
        }  in
      (ysym, y, uu____2837)
  
let new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        let uu____2873 =
          let uu___61_2874 = env  in
          let uu____2875 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____2875;
            fvar_bindings = (uu___61_2874.fvar_bindings);
            depth = (uu___61_2874.depth);
            tcenv = (uu___61_2874.tcenv);
            warn = (uu___61_2874.warn);
            cache = (uu___61_2874.cache);
            nolabels = (uu___61_2874.nolabels);
            use_zfuel_name = (uu___61_2874.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___61_2874.encode_non_total_function_typ);
            current_module_name = (uu___61_2874.current_module_name)
          }  in
        (ysym, y, uu____2873)
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___62_2899 = env  in
        let uu____2900 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____2900;
          fvar_bindings = (uu___62_2899.fvar_bindings);
          depth = (uu___62_2899.depth);
          tcenv = (uu___62_2899.tcenv);
          warn = (uu___62_2899.warn);
          cache = (uu___62_2899.cache);
          nolabels = (uu___62_2899.nolabels);
          use_zfuel_name = (uu___62_2899.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___62_2899.encode_non_total_function_typ);
          current_module_name = (uu___62_2899.current_module_name)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let uu____2919 = lookup_bvar_binding env a  in
      match uu____2919 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2931 = lookup_bvar_binding env a2  in
          (match uu____2931 with
           | FStar_Pervasives_Native.None  ->
               let uu____2942 =
                 let uu____2943 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2944 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2943 uu____2944
                  in
               failwith uu____2942
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            fvar_binding
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
  
let new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
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
        let uu____3017 =
          let uu___63_3018 = env  in
          let uu____3019 = add_fvar_binding fvb env.fvar_bindings  in
          {
            bvar_bindings = (uu___63_3018.bvar_bindings);
            fvar_bindings = uu____3019;
            depth = (uu___63_3018.depth);
            tcenv = (uu___63_3018.tcenv);
            warn = (uu___63_3018.warn);
            cache = (uu___63_3018.cache);
            nolabels = (uu___63_3018.nolabels);
            use_zfuel_name = (uu___63_3018.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___63_3018.encode_non_total_function_typ);
            current_module_name = (uu___63_3018.current_module_name)
          }  in
        (fname, ftok_name, uu____3017)
  
let lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding =
  fun env  ->
    fun a  ->
      let uu____3032 = lookup_fvar_binding env a  in
      match uu____3032 with
      | FStar_Pervasives_Native.None  ->
          let uu____3035 =
            let uu____3036 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3036  in
          failwith uu____3035
      | FStar_Pervasives_Native.Some s -> s
  
let push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            let fvb = mk_fvb x fname arity ftok FStar_Pervasives_Native.None
               in
            let uu___64_3068 = env  in
            let uu____3069 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___64_3068.bvar_bindings);
              fvar_bindings = uu____3069;
              depth = (uu___64_3068.depth);
              tcenv = (uu___64_3068.tcenv);
              warn = (uu___64_3068.warn);
              cache = (uu___64_3068.cache);
              nolabels = (uu___64_3068.nolabels);
              use_zfuel_name = (uu___64_3068.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___64_3068.encode_non_total_function_typ);
              current_module_name = (uu___64_3068.current_module_name)
            }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____3089 =
            let uu____3096 =
              let uu____3099 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____3099]  in
            (f, uu____3096)  in
          FStar_SMTEncoding_Util.mkApp uu____3089  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___65_3105 = env  in
        let uu____3106 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___65_3105.bvar_bindings);
          fvar_bindings = uu____3106;
          depth = (uu___65_3105.depth);
          tcenv = (uu___65_3105.tcenv);
          warn = (uu___65_3105.warn);
          cache = (uu___65_3105.cache);
          nolabels = (uu___65_3105.nolabels);
          use_zfuel_name = (uu___65_3105.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___65_3105.encode_non_total_function_typ);
          current_module_name = (uu___65_3105.current_module_name)
        }
  
let try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3121 = lookup_fvar_binding env l  in
      match uu____3121 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3130 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3138,fuel::[]) ->
                         let uu____3142 =
                           let uu____3143 =
                             let uu____3144 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____3144
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____3143 "fuel"  in
                         if uu____3142
                         then
                           let uu____3147 =
                             let uu____3148 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3148
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_17  ->
                                FStar_Pervasives_Native.Some _0_17)
                             uu____3147
                         else FStar_Pervasives_Native.Some t
                     | uu____3152 -> FStar_Pervasives_Native.Some t)
                | uu____3153 -> FStar_Pervasives_Native.None))
  
let lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____3170 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3170 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3174 =
            let uu____3175 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3175  in
          failwith uu____3174
  
let lookup_free_var_name :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      ((fvb.smt_id), (fvb.smt_arity))
  
let lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list,
        Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____3228;
            FStar_SMTEncoding_Term.rng = uu____3229;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.lift_native_int (1))))
      | uu____3244 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel],
                      (fvb.smt_arity + (Prims.lift_native_int (1))))
                | uu____3272 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.psmap_find_map env.fvar_bindings
        (fun uu____3289  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  