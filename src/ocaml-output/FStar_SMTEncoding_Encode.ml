open Prims
let add_fuel :
  'Auu____7 . 'Auu____7 -> 'Auu____7 Prims.list -> 'Auu____7 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____24 = FStar_Options.unthrottle_inductives ()  in
      if uu____24 then tl1 else x :: tl1
  
let withenv :
  'Auu____38 'Auu____39 'Auu____40 .
    'Auu____38 ->
      ('Auu____39,'Auu____40) FStar_Pervasives_Native.tuple2 ->
        ('Auu____39,'Auu____40,'Auu____38) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____60  -> match uu____60 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____75 'Auu____76 'Auu____77 .
    (('Auu____75,'Auu____76) FStar_Util.either,'Auu____77)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____75,'Auu____76) FStar_Util.either,'Auu____77)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___81_124  ->
         match uu___81_124 with
         | (FStar_Util.Inl uu____133,uu____134) -> false
         | uu____139 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___104_166 = a  in
        let uu____167 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____167;
          FStar_Syntax_Syntax.index =
            (uu___104_166.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___104_166.FStar_Syntax_Syntax.sort)
        }  in
      let uu____168 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____168
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____189 =
          let uu____190 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____190  in
        let uu____191 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____191 with
        | (uu____196,t) ->
            let uu____198 =
              let uu____199 = FStar_Syntax_Subst.compress t  in
              uu____199.FStar_Syntax_Syntax.n  in
            (match uu____198 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____220 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____220 with
                  | (binders,uu____226) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____241 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____252 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____252
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____263 =
        let uu____268 = mk_term_projector_name lid a  in
        (uu____268,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____263
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____279 =
        let uu____284 = mk_term_projector_name_by_pos lid i  in
        (uu____284,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____279
  
let mk_data_tester :
  'Auu____293 .
    'Auu____293 ->
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
let (__proj__Mkvarops_t__item__push : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____777 =
    let uu____778 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____781 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____778, uu____781)  in
  let scopes =
    let uu____801 = let uu____812 = new_scope ()  in [uu____812]  in
    FStar_Util.mk_ref uu____801  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____855 =
        let uu____858 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____858
          (fun uu____945  ->
             match uu____945 with
             | (names1,uu____957) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____855 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____966 ->
          (FStar_Util.incr ctr;
           (let uu____1001 =
              let uu____1002 =
                let uu____1003 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1003  in
              Prims.strcat "__" uu____1002  in
            Prims.strcat y1 uu____1001))
       in
    let top_scope =
      let uu____1052 =
        let uu____1061 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1061
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1052  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1182 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1268 =
      let uu____1269 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1269  in
    FStar_Util.format2 "%s_%s" pfx uu____1268  in
  let string_const s =
    let uu____1276 =
      let uu____1279 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1279
        (fun uu____1366  ->
           match uu____1366 with
           | (uu____1377,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1276 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1390 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1390  in
        let top_scope =
          let uu____1394 =
            let uu____1403 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1403  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1394  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1507 =
    let uu____1508 =
      let uu____1519 = new_scope ()  in
      let uu____1528 = FStar_ST.op_Bang scopes  in uu____1519 :: uu____1528
       in
    FStar_ST.op_Colon_Equals scopes uu____1508  in
  let pop1 uu____1682 =
    let uu____1683 =
      let uu____1694 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1694
       in
    FStar_ST.op_Colon_Equals scopes uu____1683  in
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
  fun x  ->
    let uu___105_1848 = x  in
    let uu____1849 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1849;
      FStar_Syntax_Syntax.index = (uu___105_1848.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___105_1848.FStar_Syntax_Syntax.sort)
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
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of fvar_binding [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1974 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____2000 -> false
  
let (__proj__Binding_fvar__item___0 : binding -> fvar_binding) =
  fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____2014 'Auu____2015 .
    'Auu____2014 ->
      ('Auu____2014,'Auu____2015 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  fun projectee  ->
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
  'Auu____2343 .
    'Auu____2343 ->
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
                 (fun uu___82_2381  ->
                    match uu___82_2381 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2385 -> []))
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
    let uu____2398 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___83_2408  ->
              match uu___83_2408 with
              | Binding_var (x,uu____2410) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid))
       in
    FStar_All.pipe_right uu____2398 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2420 .
    env_t ->
      (binding -> 'Auu____2420 FStar_Pervasives_Native.option) ->
        'Auu____2420 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2454 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2454
      then
        let uu____2457 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2457
      else FStar_Pervasives_Native.None
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2474 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2474)
  
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
      (ysym, y,
        (let uu___106_2494 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___106_2494.tcenv);
           warn = (uu___106_2494.warn);
           cache = (uu___106_2494.cache);
           nolabels = (uu___106_2494.nolabels);
           use_zfuel_name = (uu___106_2494.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___106_2494.encode_non_total_function_typ);
           current_module_name = (uu___106_2494.current_module_name)
         }))
  
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
      (ysym, y,
        (let uu___107_2516 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___107_2516.depth);
           tcenv = (uu___107_2516.tcenv);
           warn = (uu___107_2516.warn);
           cache = (uu___107_2516.cache);
           nolabels = (uu___107_2516.nolabels);
           use_zfuel_name = (uu___107_2516.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___107_2516.encode_non_total_function_typ);
           current_module_name = (uu___107_2516.current_module_name)
         }))
  
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
        (ysym, y,
          (let uu___108_2543 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___108_2543.depth);
             tcenv = (uu___108_2543.tcenv);
             warn = (uu___108_2543.warn);
             cache = (uu___108_2543.cache);
             nolabels = (uu___108_2543.nolabels);
             use_zfuel_name = (uu___108_2543.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___108_2543.encode_non_total_function_typ);
             current_module_name = (uu___108_2543.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___109_2559 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___109_2559.depth);
          tcenv = (uu___109_2559.tcenv);
          warn = (uu___109_2559.warn);
          cache = (uu___109_2559.cache);
          nolabels = (uu___109_2559.nolabels);
          use_zfuel_name = (uu___109_2559.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___109_2559.encode_non_total_function_typ);
          current_module_name = (uu___109_2559.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___84_2589  ->
             match uu___84_2589 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2602 -> FStar_Pervasives_Native.None)
         in
      let uu____2607 = aux a  in
      match uu____2607 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2619 = aux a2  in
          (match uu____2619 with
           | FStar_Pervasives_Native.None  ->
               let uu____2630 =
                 let uu____2631 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2632 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2631 uu____2632
                  in
               failwith uu____2630
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
        (fname, ftok_name,
          (let uu___110_2706 = env  in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___110_2706.depth);
             tcenv = (uu___110_2706.tcenv);
             warn = (uu___110_2706.warn);
             cache = (uu___110_2706.cache);
             nolabels = (uu___110_2706.nolabels);
             use_zfuel_name = (uu___110_2706.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___110_2706.encode_non_total_function_typ);
             current_module_name = (uu___110_2706.current_module_name)
           }))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___85_2721  ->
           match uu___85_2721 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2725 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2736 =
        lookup_binding env
          (fun uu___86_2741  ->
             match uu___86_2741 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2745 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2736 FStar_Option.isSome
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2758 = try_lookup_lid env a  in
      match uu____2758 with
      | FStar_Pervasives_Native.None  ->
          let uu____2761 =
            let uu____2762 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2762  in
          failwith uu____2761
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
            let uu___111_2794 = env  in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___111_2794.depth);
              tcenv = (uu___111_2794.tcenv);
              warn = (uu___111_2794.warn);
              cache = (uu___111_2794.cache);
              nolabels = (uu___111_2794.nolabels);
              use_zfuel_name = (uu___111_2794.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___111_2794.encode_non_total_function_typ);
              current_module_name = (uu___111_2794.current_module_name)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2812 =
            let uu____2819 =
              let uu____2822 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2822]  in
            (f, uu____2819)  in
          FStar_SMTEncoding_Util.mkApp uu____2812  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___112_2828 = env  in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___112_2828.depth);
          tcenv = (uu___112_2828.tcenv);
          warn = (uu___112_2828.warn);
          cache = (uu___112_2828.cache);
          nolabels = (uu___112_2828.nolabels);
          use_zfuel_name = (uu___112_2828.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___112_2828.encode_non_total_function_typ);
          current_module_name = (uu___112_2828.current_module_name)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2841 = try_lookup_lid env l  in
      match uu____2841 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2850 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2858,fuel::[]) ->
                         let uu____2862 =
                           let uu____2863 =
                             let uu____2864 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2864
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2863 "fuel"  in
                         if uu____2862
                         then
                           let uu____2867 =
                             let uu____2868 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2868
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_17  ->
                                FStar_Pervasives_Native.Some _0_17)
                             uu____2867
                         else FStar_Pervasives_Native.Some t
                     | uu____2872 -> FStar_Pervasives_Native.Some t)
                | uu____2873 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2890 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2890 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2894 =
            let uu____2895 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2895  in
          failwith uu____2894
  
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
            FStar_SMTEncoding_Term.freevars = uu____2948;
            FStar_SMTEncoding_Term.rng = uu____2949;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____2964 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____2992 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___87_3009  ->
           match uu___87_3009 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____3013 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3020 .
    'Auu____3020 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3040  ->
      match uu____3040 with
      | (pats,vars,body) ->
          let fallback uu____3067 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3072 = FStar_Options.unthrottle_inductives ()  in
          if uu____3072
          then fallback ()
          else
            (let uu____3074 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3074 with
             | (fsym,fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p  ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType",args) ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____3107 -> p))
                    in
                 let pats1 = FStar_List.map add_fuel1 pats  in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3128 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3128
                         | uu____3131 ->
                             let uu____3132 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3132 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3137 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1") 
let (head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3184 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3197 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3204 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3205 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3222 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3239 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3241 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3241 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3259;
             FStar_Syntax_Syntax.vars = uu____3260;_},uu____3261)
          ->
          let uu____3282 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3282 FStar_Option.isNone
      | uu____3299 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____3310 =
        let uu____3311 = FStar_Syntax_Util.un_uinst t  in
        uu____3311.FStar_Syntax_Syntax.n  in
      match uu____3310 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3314,uu____3315,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___88_3336  ->
                  match uu___88_3336 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3337 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3339 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3339 FStar_Option.isSome
      | uu____3356 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____3367 = head_normal env t  in
      if uu____3367
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
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3384 =
      let uu____3385 = FStar_Syntax_Syntax.null_binder t  in [uu____3385]  in
    let uu____3386 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3384 uu____3386 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3428 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3428
                | s ->
                    let uu____3431 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3431) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'Auu____3458 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3458
  =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____3479 =
            let uu____3484 =
              let uu____3485 = FStar_Util.string_of_int arity  in
              let uu____3486 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3485 uu____3486
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3484)  in
          FStar_Errors.raise_error uu____3479 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____3525 = FStar_Util.first_N arity args  in
               match uu____3525 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3548 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3548 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___89_3557  ->
    match uu___89_3557 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3558 -> false
  
let (is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____3604;
                       FStar_SMTEncoding_Term.rng = uu____3605;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3628) ->
              let uu____3637 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3648 -> false) args (FStar_List.rev xs))
                 in
              if uu____3637
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3652,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3656 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3660 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3660))
                 in
              if uu____3656
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3664 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3917 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3923 -> false
  
let (as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3950 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3963 ->
            let uu____3970 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3970
        | uu____3971 ->
            if norm1
            then let uu____3972 = whnf env t1  in aux false uu____3972
            else
              (let uu____3974 =
                 let uu____3975 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3976 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3975 uu____3976
                  in
               failwith uu____3974)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4010) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4015 ->
        let uu____4016 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4016)
  
let is_arithmetic_primitive :
  'Auu____4033 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4033 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4055::uu____4056::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4060::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4063 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4086 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4103 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4110 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4110)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4151)::uu____4152::uu____4153::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4204)::uu____4205::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4242 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4545 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4545, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4548 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4548, [])
      | FStar_Const.Const_char c1 ->
          let uu____4552 =
            let uu____4553 =
              let uu____4560 =
                let uu____4563 =
                  let uu____4564 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4564  in
                [uu____4563]  in
              ("FStar.Char.__char_of_int", uu____4560)  in
            FStar_SMTEncoding_Util.mkApp uu____4553  in
          (uu____4552, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4580 =
            let uu____4581 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4581  in
          (uu____4580, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4602) ->
          let uu____4603 = varops.string_const s  in (uu____4603, [])
      | FStar_Const.Const_range uu____4606 ->
          let uu____4607 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4607, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4613 =
            let uu____4614 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4614  in
          failwith uu____4613

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4643 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4643
         then
           let uu____4644 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4644
         else ());
        (let uu____4646 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4730  ->
                   fun b  ->
                     match uu____4730 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4809 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4825 = gen_term_var env1 x  in
                           match uu____4825 with
                           | (xxsym,xx,env') ->
                               let uu____4849 =
                                 let uu____4854 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4854 env1 xx
                                  in
                               (match uu____4849 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4809 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4646 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____5013 = encode_term t env  in
          match uu____5013 with
          | (t1,decls) ->
              let uu____5024 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5024, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____5035 = encode_term t env  in
          match uu____5035 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5050 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5050, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5052 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5052, decls))

and (encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5058 = encode_args args_e env  in
        match uu____5058 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5077 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5088 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5088  in
            let binary arg_tms1 =
              let uu____5103 =
                let uu____5104 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5104  in
              let uu____5105 =
                let uu____5106 =
                  let uu____5107 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5107  in
                FStar_SMTEncoding_Term.unboxInt uu____5106  in
              (uu____5103, uu____5105)  in
            let mk_default uu____5115 =
              let uu____5116 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5116 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____5178 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5178
              then
                let uu____5179 =
                  let uu____5180 = mk_args ts  in op uu____5180  in
                FStar_All.pipe_right uu____5179 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5215 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5215
              then
                let uu____5216 = binary ts  in
                match uu____5216 with
                | (t1,t2) ->
                    let uu____5223 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5223
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5227 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5227
                 then
                   let uu____5228 =
                     let uu____5229 = binary ts  in op uu____5229  in
                   FStar_All.pipe_right uu____5228
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____5390 =
              let uu____5400 =
                FStar_List.tryFind
                  (fun uu____5424  ->
                     match uu____5424 with
                     | (l,uu____5434) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5400 FStar_Util.must  in
            (match uu____5390 with
             | (uu____5478,op) ->
                 let uu____5490 = op arg_tms  in (uu____5490, decls))

and (encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5498 = FStar_List.hd args_e  in
        match uu____5498 with
        | (tm_sz,uu____5506) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5516 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5516 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____5524 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5524);
                   t_decls1)
               in
            let uu____5525 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5545::(sz_arg,uu____5547)::uu____5548::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5597 =
                    let uu____5600 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5600  in
                  let uu____5603 =
                    let uu____5606 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5606  in
                  (uu____5597, uu____5603)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5612::(sz_arg,uu____5614)::uu____5615::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5664 =
                    let uu____5665 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5665
                     in
                  failwith uu____5664
              | uu____5674 ->
                  let uu____5681 = FStar_List.tail args_e  in
                  (uu____5681, FStar_Pervasives_Native.None)
               in
            (match uu____5525 with
             | (arg_tms,ext_sz) ->
                 let uu____5704 = encode_args arg_tms env  in
                 (match uu____5704 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5725 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5736 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5736  in
                      let unary_arith arg_tms2 =
                        let uu____5747 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5747  in
                      let binary arg_tms2 =
                        let uu____5762 =
                          let uu____5763 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5763
                           in
                        let uu____5764 =
                          let uu____5765 =
                            let uu____5766 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5766  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5765
                           in
                        (uu____5762, uu____5764)  in
                      let binary_arith arg_tms2 =
                        let uu____5783 =
                          let uu____5784 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5784
                           in
                        let uu____5785 =
                          let uu____5786 =
                            let uu____5787 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5787  in
                          FStar_SMTEncoding_Term.unboxInt uu____5786  in
                        (uu____5783, uu____5785)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____5845 =
                          let uu____5846 = mk_args ts  in op uu____5846  in
                        FStar_All.pipe_right uu____5845 resBox  in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____5978 =
                          let uu____5983 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5983  in
                        let uu____5985 =
                          let uu____5990 =
                            let uu____5991 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5991  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5990  in
                        mk_bv uu____5978 unary uu____5985 arg_tms2  in
                      let to_int1 =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
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
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____6224 =
                        let uu____6234 =
                          FStar_List.tryFind
                            (fun uu____6258  ->
                               match uu____6258 with
                               | (l,uu____6268) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6234 FStar_Util.must  in
                      (match uu____6224 with
                       | (uu____6314,op) ->
                           let uu____6326 = op arg_tms1  in
                           (uu____6326, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6337 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6337
       then
         let uu____6338 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6339 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6340 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6338 uu____6339
           uu____6340
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6346 ->
           let uu____6371 =
             let uu____6372 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6373 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6374 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6375 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6372
               uu____6373 uu____6374 uu____6375
              in
           failwith uu____6371
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6380 =
             let uu____6381 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6382 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6383 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6384 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6381
               uu____6382 uu____6383 uu____6384
              in
           failwith uu____6380
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6390 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____6390 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6392 =
             let uu____6393 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6393
              in
           failwith uu____6392
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____6400),uu____6401) ->
           let uu____6450 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____6458 -> false  in
           if uu____6450
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____6475) ->
           let tv =
             let uu____6481 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____6481
              in
           let t1 =
             let uu____6485 =
               let uu____6494 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____6494]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____6485
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6496) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6506 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6506, [])
       | FStar_Syntax_Syntax.Tm_type uu____6509 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6513) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6538 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6538 with
            | (binders1,res) ->
                let uu____6549 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6549
                then
                  let uu____6554 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6554 with
                   | (vars,guards,env',decls,uu____6579) ->
                       let fsym =
                         let uu____6597 = varops.fresh "f"  in
                         (uu____6597, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6600 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___113_6609 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___113_6609.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___113_6609.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___113_6609.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___113_6609.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___113_6609.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___113_6609.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___113_6609.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___113_6609.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___113_6609.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___113_6609.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___113_6609.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___113_6609.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___113_6609.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___113_6609.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___113_6609.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___113_6609.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___113_6609.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___113_6609.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___113_6609.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___113_6609.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___113_6609.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___113_6609.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___113_6609.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___113_6609.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___113_6609.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___113_6609.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___113_6609.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___113_6609.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___113_6609.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___113_6609.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___113_6609.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___113_6609.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___113_6609.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___113_6609.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___113_6609.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___113_6609.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6600 with
                        | (pre_opt,res_t) ->
                            let uu____6620 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6620 with
                             | (res_pred,decls') ->
                                 let uu____6631 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6644 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6644, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6648 =
                                         encode_formula pre env'  in
                                       (match uu____6648 with
                                        | (guard,decls0) ->
                                            let uu____6661 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6661, decls0))
                                    in
                                 (match uu____6631 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6673 =
                                          let uu____6684 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6684)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6673
                                         in
                                      let cvars =
                                        let uu____6702 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6702
                                          (FStar_List.filter
                                             (fun uu____6716  ->
                                                match uu____6716 with
                                                | (x,uu____6722) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____6741 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6741 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6749 =
                                             let uu____6750 =
                                               let uu____6757 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6757)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6750
                                              in
                                           (uu____6749,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6777 =
                                               let uu____6778 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6778
                                                in
                                             varops.mk_unique uu____6777  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6789 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6789
                                             then
                                               let uu____6792 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6792
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____6800 =
                                               let uu____6807 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6807)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6800
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____6819 =
                                               let uu____6826 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6826,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6819
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____6847 =
                                               let uu____6854 =
                                                 let uu____6855 =
                                                   let uu____6866 =
                                                     let uu____6867 =
                                                       let uu____6872 =
                                                         let uu____6873 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6873
                                                          in
                                                       (f_has_t, uu____6872)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6867
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6866)
                                                    in
                                                 mkForall_fuel uu____6855  in
                                               (uu____6854,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6847
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6896 =
                                               let uu____6903 =
                                                 let uu____6904 =
                                                   let uu____6915 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6915)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6904
                                                  in
                                               (uu____6903,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6896
                                              in
                                           let t_decls1 =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____6940 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6940);
                                            (t1, t_decls1)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____6955 =
                       let uu____6962 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6962,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6955  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6974 =
                       let uu____6981 =
                         let uu____6982 =
                           let uu____6993 =
                             let uu____6994 =
                               let uu____6999 =
                                 let uu____7000 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____7000
                                  in
                               (f_has_t, uu____6999)  in
                             FStar_SMTEncoding_Util.mkImp uu____6994  in
                           ([[f_has_t]], [fsym], uu____6993)  in
                         mkForall_fuel uu____6982  in
                       (uu____6981, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6974  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____7027 ->
           let uu____7034 =
             let uu____7039 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____7039 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____7046;
                 FStar_Syntax_Syntax.vars = uu____7047;_} ->
                 let uu____7054 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____7054 with
                  | (b,f1) ->
                      let uu____7079 =
                        let uu____7080 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7080  in
                      (uu____7079, f1))
             | uu____7089 -> failwith "impossible"  in
           (match uu____7034 with
            | (x,f) ->
                let uu____7100 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7100 with
                 | (base_t,decls) ->
                     let uu____7111 = gen_term_var env x  in
                     (match uu____7111 with
                      | (x1,xtm,env') ->
                          let uu____7125 = encode_formula f env'  in
                          (match uu____7125 with
                           | (refinement,decls') ->
                               let uu____7136 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7136 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____7152 =
                                        let uu____7155 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7162 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7155
                                          uu____7162
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7152
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7195  ->
                                              match uu____7195 with
                                              | (y,uu____7201) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____7234 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7234 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7242 =
                                           let uu____7243 =
                                             let uu____7250 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7250)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7243
                                            in
                                         (uu____7242,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7271 =
                                             let uu____7272 =
                                               let uu____7273 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7273
                                                in
                                             Prims.strcat module_name
                                               uu____7272
                                              in
                                           varops.mk_unique uu____7271  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____7287 =
                                             let uu____7294 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7294)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7287
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____7309 =
                                             let uu____7316 =
                                               let uu____7317 =
                                                 let uu____7328 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7328)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7317
                                                in
                                             (uu____7316,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7309
                                            in
                                         let t_kinding =
                                           let uu____7346 =
                                             let uu____7353 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7353,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7346
                                            in
                                         let t_interp =
                                           let uu____7371 =
                                             let uu____7378 =
                                               let uu____7379 =
                                                 let uu____7390 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7390)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7379
                                                in
                                             let uu____7413 =
                                               let uu____7416 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7416
                                                in
                                             (uu____7378, uu____7413,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7371
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7423 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7423);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7453 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7453  in
           let uu____7454 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____7454 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7466 =
                    let uu____7473 =
                      let uu____7474 =
                        let uu____7475 =
                          let uu____7476 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7476
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7475  in
                      varops.mk_unique uu____7474  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7473)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7466  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7481 ->
           let uu____7496 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7496 with
            | (head1,args_e) ->
                let uu____7537 =
                  let uu____7550 =
                    let uu____7551 = FStar_Syntax_Subst.compress head1  in
                    uu____7551.FStar_Syntax_Syntax.n  in
                  (uu____7550, args_e)  in
                (match uu____7537 with
                 | uu____7566 when head_redex env head1 ->
                     let uu____7579 = whnf env t  in
                     encode_term uu____7579 env
                 | uu____7580 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7599 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7613;
                       FStar_Syntax_Syntax.vars = uu____7614;_},uu____7615),uu____7616::
                    (v1,uu____7618)::(v2,uu____7620)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7671 = encode_term v1 env  in
                     (match uu____7671 with
                      | (v11,decls1) ->
                          let uu____7682 = encode_term v2 env  in
                          (match uu____7682 with
                           | (v21,decls2) ->
                               let uu____7693 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7693,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7697::(v1,uu____7699)::(v2,uu____7701)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7748 = encode_term v1 env  in
                     (match uu____7748 with
                      | (v11,decls1) ->
                          let uu____7759 = encode_term v2 env  in
                          (match uu____7759 with
                           | (v21,decls2) ->
                               let uu____7770 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7770,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7774)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7800)::(rng,uu____7802)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7837) ->
                     let e0 =
                       let uu____7855 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7855
                        in
                     ((let uu____7863 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7863
                       then
                         let uu____7864 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7864
                       else ());
                      (let e =
                         let uu____7869 =
                           let uu____7874 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7875 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7874
                             uu____7875
                            in
                         uu____7869 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7884),(arg,uu____7886)::[]) -> encode_term arg env
                 | uu____7911 ->
                     let uu____7924 = encode_args args_e env  in
                     (match uu____7924 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7981 = encode_term head1 env  in
                            match uu____7981 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____8045 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____8045 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8123  ->
                                                 fun uu____8124  ->
                                                   match (uu____8123,
                                                           uu____8124)
                                                   with
                                                   | ((bv,uu____8146),
                                                      (a,uu____8148)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8166 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8166
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8171 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8171 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8186 =
                                                   let uu____8193 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8202 =
                                                     let uu____8203 =
                                                       let uu____8204 =
                                                         let uu____8205 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8205
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8204
                                                        in
                                                     varops.mk_unique
                                                       uu____8203
                                                      in
                                                   (uu____8193,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8202)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8186
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8224 = lookup_free_var_sym env fv  in
                            match uu____8224 with
                            | (fname,fuel_args,arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args)
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____8256;
                                   FStar_Syntax_Syntax.vars = uu____8257;_},uu____8258)
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
                                   FStar_Syntax_Syntax.pos = uu____8269;
                                   FStar_Syntax_Syntax.vars = uu____8270;_},uu____8271)
                                ->
                                let uu____8276 =
                                  let uu____8277 =
                                    let uu____8282 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8282
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8277
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8276
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8312 =
                                  let uu____8313 =
                                    let uu____8318 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8318
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8313
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8312
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8347,(FStar_Util.Inl t1,uu____8349),uu____8350)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8399,(FStar_Util.Inr c,uu____8401),uu____8402)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8451 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8478 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8478
                                  in
                               let uu____8479 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8479 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8495;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8496;_},uu____8497)
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
                                     | uu____8511 ->
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
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____8560 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8560 with
            | (bs1,body1,opening) ->
                let fallback uu____8585 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8592 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8592, [decl])  in
                let is_impure rc =
                  let uu____8601 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8601 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8613 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____8613
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8631 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8631
                  then
                    let uu____8634 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8634
                  else
                    (let uu____8636 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8636
                     then
                       let uu____8639 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8639
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8646 =
                         let uu____8651 =
                           let uu____8652 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8652
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8651)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8646);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8654 =
                       (is_impure rc) &&
                         (let uu____8656 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8656)
                        in
                     if uu____8654
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8663 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8663 with
                        | (vars,guards,envbody,decls,uu____8688) ->
                            let body2 =
                              let uu____8702 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8702
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8704 = encode_term body2 envbody  in
                            (match uu____8704 with
                             | (body3,decls') ->
                                 let uu____8715 =
                                   let uu____8724 = codomain_eff rc  in
                                   match uu____8724 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8743 = encode_term tfun env
                                          in
                                       (match uu____8743 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8715 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8775 =
                                          let uu____8786 =
                                            let uu____8787 =
                                              let uu____8792 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8792, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8787
                                             in
                                          ([], vars, uu____8786)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8775
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8804 =
                                              let uu____8807 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8807
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8804
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8826 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8826 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8834 =
                                             let uu____8835 =
                                               let uu____8842 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8842)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8835
                                              in
                                           (uu____8834,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8853 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8853 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8864 =
                                                    let uu____8865 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8865 = cache_size
                                                     in
                                                  if uu____8864
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____8881 =
                                                      let uu____8882 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8882
                                                       in
                                                    varops.mk_unique
                                                      uu____8881
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____8889 =
                                                    let uu____8896 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8896)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8889
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____8914 =
                                                        let uu____8915 =
                                                          let uu____8922 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8922,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8915
                                                         in
                                                      [uu____8914]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8935 =
                                                    let uu____8942 =
                                                      let uu____8943 =
                                                        let uu____8954 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8954)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8943
                                                       in
                                                    (uu____8942,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8935
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____8971 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8971);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8974,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8975;
                          FStar_Syntax_Syntax.lbunivs = uu____8976;
                          FStar_Syntax_Syntax.lbtyp = uu____8977;
                          FStar_Syntax_Syntax.lbeff = uu____8978;
                          FStar_Syntax_Syntax.lbdef = uu____8979;
                          FStar_Syntax_Syntax.lbattrs = uu____8980;
                          FStar_Syntax_Syntax.lbpos = uu____8981;_}::uu____8982),uu____8983)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____9013;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____9015;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____9017;
                FStar_Syntax_Syntax.lbpos = uu____9018;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____9042 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
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
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____9112 =
                let uu____9117 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9117 env  in
              match uu____9112 with
              | (ee1,decls1) ->
                  let uu____9138 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9138 with
                   | (xs,e21) ->
                       let uu____9163 = FStar_List.hd xs  in
                       (match uu____9163 with
                        | (x1,uu____9177) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9179 = encode_body e21 env'  in
                            (match uu____9179 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____9211 =
              let uu____9218 =
                let uu____9219 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9219  in
              gen_term_var env uu____9218  in
            match uu____9211 with
            | (scrsym,scr',env1) ->
                let uu____9227 = encode_term e env1  in
                (match uu____9227 with
                 | (scr,decls) ->
                     let uu____9238 =
                       let encode_branch b uu____9267 =
                         match uu____9267 with
                         | (else_case,decls1) ->
                             let uu____9286 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9286 with
                              | (p,w,br) ->
                                  let uu____9312 = encode_pat env1 p  in
                                  (match uu____9312 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9349  ->
                                                   match uu____9349 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9356 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9378 =
                                               encode_term w1 env2  in
                                             (match uu____9378 with
                                              | (w2,decls2) ->
                                                  let uu____9391 =
                                                    let uu____9392 =
                                                      let uu____9397 =
                                                        let uu____9398 =
                                                          let uu____9403 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9403)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9398
                                                         in
                                                      (guard, uu____9397)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9392
                                                     in
                                                  (uu____9391, decls2))
                                          in
                                       (match uu____9356 with
                                        | (guard1,decls2) ->
                                            let uu____9416 =
                                              encode_br br env2  in
                                            (match uu____9416 with
                                             | (br1,decls3) ->
                                                 let uu____9429 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9429,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9238 with
                      | (match_tm,decls1) ->
                          let uu____9448 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9448, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____9488 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9488
       then
         let uu____9489 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9489
       else ());
      (let uu____9491 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9491 with
       | (vars,pat_term) ->
           let uu____9508 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9561  ->
                     fun v1  ->
                       match uu____9561 with
                       | (env1,vars1) ->
                           let uu____9613 = gen_term_var env1 v1  in
                           (match uu____9613 with
                            | (xx,uu____9635,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9508 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9718 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9719 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9720 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9728 = encode_const c env1  in
                      (match uu____9728 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9742::uu____9743 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9746 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9769 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9769 with
                        | (uu____9776,uu____9777::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9780 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9813  ->
                                  match uu____9813 with
                                  | (arg,uu____9821) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9827 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9827))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9858) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9889 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9912 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9956  ->
                                  match uu____9956 with
                                  | (arg,uu____9970) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9976 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9976))
                         in
                      FStar_All.pipe_right uu____9912 FStar_List.flatten
                   in
                let pat_term1 uu____10006 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____10016 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10054  ->
                fun uu____10055  ->
                  match (uu____10054, uu____10055) with
                  | ((tms,decls),(t,uu____10091)) ->
                      let uu____10112 = encode_term t env  in
                      (match uu____10112 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10016 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10171 = FStar_Syntax_Util.list_elements e  in
        match uu____10171 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____10194 =
          let uu____10209 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10209 FStar_Syntax_Util.head_and_args
           in
        match uu____10194 with
        | (head1,args) ->
            let uu____10248 =
              let uu____10261 =
                let uu____10262 = FStar_Syntax_Util.un_uinst head1  in
                uu____10262.FStar_Syntax_Syntax.n  in
              (uu____10261, args)  in
            (match uu____10248 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10276,uu____10277)::(e,uu____10279)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10314 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____10354 =
            let uu____10369 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10369 FStar_Syntax_Util.head_and_args
             in
          match uu____10354 with
          | (head1,args) ->
              let uu____10410 =
                let uu____10423 =
                  let uu____10424 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10424.FStar_Syntax_Syntax.n  in
                (uu____10423, args)  in
              (match uu____10410 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10441)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10468 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10490 = smt_pat_or t1  in
            (match uu____10490 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10506 = list_elements1 e  in
                 FStar_All.pipe_right uu____10506
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10524 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10524
                           (FStar_List.map one_pat)))
             | uu____10535 ->
                 let uu____10540 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10540])
        | uu____10561 ->
            let uu____10564 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10564]
         in
      let uu____10585 =
        let uu____10604 =
          let uu____10605 = FStar_Syntax_Subst.compress t  in
          uu____10605.FStar_Syntax_Syntax.n  in
        match uu____10604 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10644 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10644 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10687;
                        FStar_Syntax_Syntax.effect_name = uu____10688;
                        FStar_Syntax_Syntax.result_typ = uu____10689;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10691)::(post,uu____10693)::(pats,uu____10695)::[];
                        FStar_Syntax_Syntax.flags = uu____10696;_}
                      ->
                      let uu____10737 = lemma_pats pats  in
                      (binders1, pre, post, uu____10737)
                  | uu____10754 -> failwith "impos"))
        | uu____10773 -> failwith "Impos"  in
      match uu____10585 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___114_10821 = env  in
            {
              bindings = (uu___114_10821.bindings);
              depth = (uu___114_10821.depth);
              tcenv = (uu___114_10821.tcenv);
              warn = (uu___114_10821.warn);
              cache = (uu___114_10821.cache);
              nolabels = (uu___114_10821.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___114_10821.encode_non_total_function_typ);
              current_module_name = (uu___114_10821.current_module_name)
            }  in
          let uu____10822 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10822 with
           | (vars,guards,env2,decls,uu____10847) ->
               let uu____10860 =
                 let uu____10875 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10929 =
                             let uu____10940 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10940
                               FStar_List.unzip
                              in
                           match uu____10929 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10875 FStar_List.unzip  in
               (match uu____10860 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___115_11092 = env2  in
                      {
                        bindings = (uu___115_11092.bindings);
                        depth = (uu___115_11092.depth);
                        tcenv = (uu___115_11092.tcenv);
                        warn = (uu___115_11092.warn);
                        cache = (uu___115_11092.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___115_11092.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___115_11092.encode_non_total_function_typ);
                        current_module_name =
                          (uu___115_11092.current_module_name)
                      }  in
                    let uu____11093 =
                      let uu____11098 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____11098 env3  in
                    (match uu____11093 with
                     | (pre1,decls'') ->
                         let uu____11105 =
                           let uu____11110 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____11110 env3  in
                         (match uu____11105 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____11120 =
                                let uu____11121 =
                                  let uu____11132 =
                                    let uu____11133 =
                                      let uu____11138 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____11138, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____11133
                                     in
                                  (pats, vars, uu____11132)  in
                                FStar_SMTEncoding_Util.mkForall uu____11121
                                 in
                              (uu____11120, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11151 = FStar_Syntax_Util.head_and_args t  in
      match uu____11151 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11210::(x,uu____11212)::(t1,uu____11214)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11261 = encode_term x env  in
               (match uu____11261 with
                | (x1,decls) ->
                    let uu____11274 = encode_term t1 env  in
                    (match uu____11274 with
                     | (t2,decls') ->
                         let uu____11287 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11287, (FStar_List.append decls decls'))))
           | uu____11290 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11315 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11315
        then
          let uu____11316 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11317 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11316 uu____11317
        else ()  in
      let enc f r l =
        let uu____11356 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11384 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11384 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11356 with
        | (decls,args) ->
            let uu____11413 =
              let uu___116_11414 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___116_11414.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___116_11414.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11413, decls)
         in
      let const_op f r uu____11451 =
        let uu____11464 = f r  in (uu____11464, [])  in
      let un_op f l =
        let uu____11487 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11487  in
      let bin_op f uu___90_11507 =
        match uu___90_11507 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11518 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11558 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11581  ->
                 match uu____11581 with
                 | (t,uu____11595) ->
                     let uu____11596 = encode_formula t env  in
                     (match uu____11596 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11558 with
        | (decls,phis) ->
            let uu____11625 =
              let uu___117_11626 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11626.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11626.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11625, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11691  ->
               match uu____11691 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11710) -> false
                    | uu____11711 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11726 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11726
        else
          (let uu____11740 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11740 r rf)
         in
      let mk_imp1 r uu___91_11775 =
        match uu___91_11775 with
        | (lhs,uu____11781)::(rhs,uu____11783)::[] ->
            let uu____11810 = encode_formula rhs env  in
            (match uu____11810 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11825) ->
                      (l1, decls1)
                  | uu____11830 ->
                      let uu____11831 = encode_formula lhs env  in
                      (match uu____11831 with
                       | (l2,decls2) ->
                           let uu____11842 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11842, (FStar_List.append decls1 decls2)))))
        | uu____11845 -> failwith "impossible"  in
      let mk_ite r uu___92_11872 =
        match uu___92_11872 with
        | (guard,uu____11878)::(_then,uu____11880)::(_else,uu____11882)::[]
            ->
            let uu____11919 = encode_formula guard env  in
            (match uu____11919 with
             | (g,decls1) ->
                 let uu____11930 = encode_formula _then env  in
                 (match uu____11930 with
                  | (t,decls2) ->
                      let uu____11941 = encode_formula _else env  in
                      (match uu____11941 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11955 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11984 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11984  in
      let connectives =
        let uu____12004 =
          let uu____12019 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____12019)  in
        let uu____12042 =
          let uu____12059 =
            let uu____12074 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____12074)  in
          let uu____12097 =
            let uu____12114 =
              let uu____12132 =
                let uu____12147 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12147)  in
              let uu____12170 =
                let uu____12187 =
                  let uu____12205 =
                    let uu____12220 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12220)  in
                  [uu____12205;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12187  in
              uu____12132 :: uu____12170  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____12114  in
          uu____12059 :: uu____12097  in
        uu____12004 :: uu____12042  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12587 = encode_formula phi' env  in
            (match uu____12587 with
             | (phi2,decls) ->
                 let uu____12598 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12598, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12599 ->
            let uu____12606 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12606 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12645 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12645 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12657;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12659;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12661;
                 FStar_Syntax_Syntax.lbpos = uu____12662;_}::[]),e2)
            ->
            let uu____12686 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12686 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12733::(x,uu____12735)::(t,uu____12737)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12784 = encode_term x env  in
                 (match uu____12784 with
                  | (x1,decls) ->
                      let uu____12795 = encode_term t env  in
                      (match uu____12795 with
                       | (t1,decls') ->
                           let uu____12806 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12806, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12811)::(msg,uu____12813)::(phi2,uu____12815)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12860 =
                   let uu____12865 =
                     let uu____12866 = FStar_Syntax_Subst.compress r  in
                     uu____12866.FStar_Syntax_Syntax.n  in
                   let uu____12869 =
                     let uu____12870 = FStar_Syntax_Subst.compress msg  in
                     uu____12870.FStar_Syntax_Syntax.n  in
                   (uu____12865, uu____12869)  in
                 (match uu____12860 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12879))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12885 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12892)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12917 when head_redex env head2 ->
                 let uu____12930 = whnf env phi1  in
                 encode_formula uu____12930 env
             | uu____12931 ->
                 let uu____12944 = encode_term phi1 env  in
                 (match uu____12944 with
                  | (tt,decls) ->
                      let uu____12955 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___118_12958 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___118_12958.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___118_12958.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12955, decls)))
        | uu____12959 ->
            let uu____12960 = encode_term phi1 env  in
            (match uu____12960 with
             | (tt,decls) ->
                 let uu____12971 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___119_12974 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___119_12974.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___119_12974.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12971, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____13018 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____13018 with
        | (vars,guards,env2,decls,uu____13057) ->
            let uu____13070 =
              let uu____13083 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____13135 =
                          let uu____13146 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____13186  ->
                                    match uu____13186 with
                                    | (t,uu____13200) ->
                                        encode_smt_pattern t
                                          (let uu___120_13206 = env2  in
                                           {
                                             bindings =
                                               (uu___120_13206.bindings);
                                             depth = (uu___120_13206.depth);
                                             tcenv = (uu___120_13206.tcenv);
                                             warn = (uu___120_13206.warn);
                                             cache = (uu___120_13206.cache);
                                             nolabels =
                                               (uu___120_13206.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___120_13206.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___120_13206.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____13146 FStar_List.unzip
                           in
                        match uu____13135 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____13083 FStar_List.unzip  in
            (match uu____13070 with
             | (pats,decls') ->
                 let uu____13315 = encode_formula body env2  in
                 (match uu____13315 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13347;
                             FStar_SMTEncoding_Term.rng = uu____13348;_}::[])::[]
                            when
                            let uu____13363 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13363 = gf -> []
                        | uu____13364 -> guards  in
                      let uu____13369 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13369, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____13433  ->
                   match uu____13433 with
                   | (x,uu____13439) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____13447 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13459 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____13459) uu____13447 tl1
                in
             let uu____13462 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13489  ->
                       match uu____13489 with
                       | (b,uu____13495) ->
                           let uu____13496 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____13496))
                in
             (match uu____13462 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13502) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____13516 =
                    let uu____13521 =
                      let uu____13522 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13522
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13521)
                     in
                  FStar_Errors.log_issue pos uu____13516)
          in
       let uu____13523 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13523 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13532 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13598  ->
                     match uu____13598 with
                     | (l,uu____13612) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13532 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13651,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13697 = encode_q_body env vars pats body  in
             match uu____13697 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13742 =
                     let uu____13753 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13753)  in
                   FStar_SMTEncoding_Term.mkForall uu____13742
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13772 = encode_q_body env vars pats body  in
             match uu____13772 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13816 =
                   let uu____13817 =
                     let uu____13828 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13828)  in
                   FStar_SMTEncoding_Term.mkExists uu____13817
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13816, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let (prims : prims_t) =
  let uu____13950 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13950 with
  | (asym,a) ->
      let uu____13957 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13957 with
       | (xsym,x) ->
           let uu____13964 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13964 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____14018 =
                      let uu____14029 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____14029, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____14018  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____14055 =
                      let uu____14062 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____14062)  in
                    FStar_SMTEncoding_Util.mkApp uu____14055  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____14075 =
                    let uu____14078 =
                      let uu____14081 =
                        let uu____14084 =
                          let uu____14085 =
                            let uu____14092 =
                              let uu____14093 =
                                let uu____14104 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____14104)  in
                              FStar_SMTEncoding_Util.mkForall uu____14093  in
                            (uu____14092, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____14085  in
                        let uu____14121 =
                          let uu____14124 =
                            let uu____14125 =
                              let uu____14132 =
                                let uu____14133 =
                                  let uu____14144 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____14144)  in
                                FStar_SMTEncoding_Util.mkForall uu____14133
                                 in
                              (uu____14132,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____14125  in
                          [uu____14124]  in
                        uu____14084 :: uu____14121  in
                      xtok_decl :: uu____14081  in
                    xname_decl :: uu____14078  in
                  (xtok1, (FStar_List.length vars), uu____14075)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____14242 =
                    let uu____14258 =
                      let uu____14271 =
                        let uu____14272 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____14272
                         in
                      quant axy uu____14271  in
                    (FStar_Parser_Const.op_Eq, uu____14258)  in
                  let uu____14284 =
                    let uu____14302 =
                      let uu____14318 =
                        let uu____14331 =
                          let uu____14332 =
                            let uu____14333 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14333  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14332
                           in
                        quant axy uu____14331  in
                      (FStar_Parser_Const.op_notEq, uu____14318)  in
                    let uu____14345 =
                      let uu____14363 =
                        let uu____14379 =
                          let uu____14392 =
                            let uu____14393 =
                              let uu____14394 =
                                let uu____14399 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14400 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14399, uu____14400)  in
                              FStar_SMTEncoding_Util.mkLT uu____14394  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14393
                             in
                          quant xy uu____14392  in
                        (FStar_Parser_Const.op_LT, uu____14379)  in
                      let uu____14412 =
                        let uu____14430 =
                          let uu____14446 =
                            let uu____14459 =
                              let uu____14460 =
                                let uu____14461 =
                                  let uu____14466 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14467 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14466, uu____14467)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14461  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14460
                               in
                            quant xy uu____14459  in
                          (FStar_Parser_Const.op_LTE, uu____14446)  in
                        let uu____14479 =
                          let uu____14497 =
                            let uu____14513 =
                              let uu____14526 =
                                let uu____14527 =
                                  let uu____14528 =
                                    let uu____14533 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14534 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14533, uu____14534)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14528  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14527
                                 in
                              quant xy uu____14526  in
                            (FStar_Parser_Const.op_GT, uu____14513)  in
                          let uu____14546 =
                            let uu____14564 =
                              let uu____14580 =
                                let uu____14593 =
                                  let uu____14594 =
                                    let uu____14595 =
                                      let uu____14600 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14601 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14600, uu____14601)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14595
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14594
                                   in
                                quant xy uu____14593  in
                              (FStar_Parser_Const.op_GTE, uu____14580)  in
                            let uu____14613 =
                              let uu____14631 =
                                let uu____14647 =
                                  let uu____14660 =
                                    let uu____14661 =
                                      let uu____14662 =
                                        let uu____14667 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14668 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14667, uu____14668)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14662
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14661
                                     in
                                  quant xy uu____14660  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14647)
                                 in
                              let uu____14680 =
                                let uu____14698 =
                                  let uu____14714 =
                                    let uu____14727 =
                                      let uu____14728 =
                                        let uu____14729 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14729
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14728
                                       in
                                    quant qx uu____14727  in
                                  (FStar_Parser_Const.op_Minus, uu____14714)
                                   in
                                let uu____14741 =
                                  let uu____14759 =
                                    let uu____14775 =
                                      let uu____14788 =
                                        let uu____14789 =
                                          let uu____14790 =
                                            let uu____14795 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14796 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14795, uu____14796)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14790
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14789
                                         in
                                      quant xy uu____14788  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14775)
                                     in
                                  let uu____14808 =
                                    let uu____14826 =
                                      let uu____14842 =
                                        let uu____14855 =
                                          let uu____14856 =
                                            let uu____14857 =
                                              let uu____14862 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14863 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14862, uu____14863)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14857
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14856
                                           in
                                        quant xy uu____14855  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14842)
                                       in
                                    let uu____14875 =
                                      let uu____14893 =
                                        let uu____14909 =
                                          let uu____14922 =
                                            let uu____14923 =
                                              let uu____14924 =
                                                let uu____14929 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14930 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14929, uu____14930)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14924
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14923
                                             in
                                          quant xy uu____14922  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14909)
                                         in
                                      let uu____14942 =
                                        let uu____14960 =
                                          let uu____14976 =
                                            let uu____14989 =
                                              let uu____14990 =
                                                let uu____14991 =
                                                  let uu____14996 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14997 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14996, uu____14997)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14991
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14990
                                               in
                                            quant xy uu____14989  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14976)
                                           in
                                        let uu____15009 =
                                          let uu____15027 =
                                            let uu____15043 =
                                              let uu____15056 =
                                                let uu____15057 =
                                                  let uu____15058 =
                                                    let uu____15063 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____15064 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____15063,
                                                      uu____15064)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15058
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____15057
                                                 in
                                              quant xy uu____15056  in
                                            (FStar_Parser_Const.op_And,
                                              uu____15043)
                                             in
                                          let uu____15076 =
                                            let uu____15094 =
                                              let uu____15110 =
                                                let uu____15123 =
                                                  let uu____15124 =
                                                    let uu____15125 =
                                                      let uu____15130 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____15131 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____15130,
                                                        uu____15131)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____15125
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____15124
                                                   in
                                                quant xy uu____15123  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____15110)
                                               in
                                            let uu____15143 =
                                              let uu____15161 =
                                                let uu____15177 =
                                                  let uu____15190 =
                                                    let uu____15191 =
                                                      let uu____15192 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____15192
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____15191
                                                     in
                                                  quant qx uu____15190  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____15177)
                                                 in
                                              [uu____15161]  in
                                            uu____15094 :: uu____15143  in
                                          uu____15027 :: uu____15076  in
                                        uu____14960 :: uu____15009  in
                                      uu____14893 :: uu____14942  in
                                    uu____14826 :: uu____14875  in
                                  uu____14759 :: uu____14808  in
                                uu____14698 :: uu____14741  in
                              uu____14631 :: uu____14680  in
                            uu____14564 :: uu____14613  in
                          uu____14497 :: uu____14546  in
                        uu____14430 :: uu____14479  in
                      uu____14363 :: uu____14412  in
                    uu____14302 :: uu____14345  in
                  uu____14242 :: uu____14284  in
                let mk1 l v1 =
                  let uu____15463 =
                    let uu____15474 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15544  ->
                              match uu____15544 with
                              | (l',uu____15560) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____15474
                      (FStar_Option.map
                         (fun uu____15636  ->
                            match uu____15636 with | (uu____15659,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____15463 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15750  ->
                          match uu____15750 with
                          | (l',uu____15766) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____15816 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15816 with
        | (xxsym,xx) ->
            let uu____15823 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15823 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15833 =
                   let uu____15840 =
                     let uu____15841 =
                       let uu____15852 =
                         let uu____15853 =
                           let uu____15858 =
                             let uu____15859 =
                               let uu____15864 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15864)  in
                             FStar_SMTEncoding_Util.mkEq uu____15859  in
                           (xx_has_type, uu____15858)  in
                         FStar_SMTEncoding_Util.mkImp uu____15853  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15852)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15841  in
                   let uu____15889 =
                     let uu____15890 =
                       let uu____15891 =
                         let uu____15892 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15892  in
                       Prims.strcat module_name uu____15891  in
                     varops.mk_unique uu____15890  in
                   (uu____15840, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15889)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15833)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____15942 =
      let uu____15943 =
        let uu____15950 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15950, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15943  in
    let uu____15953 =
      let uu____15956 =
        let uu____15957 =
          let uu____15964 =
            let uu____15965 =
              let uu____15976 =
                let uu____15977 =
                  let uu____15982 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15982)  in
                FStar_SMTEncoding_Util.mkImp uu____15977  in
              ([[typing_pred]], [xx], uu____15976)  in
            mkForall_fuel uu____15965  in
          (uu____15964, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15957  in
      [uu____15956]  in
    uu____15942 :: uu____15953  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16030 =
      let uu____16031 =
        let uu____16038 =
          let uu____16039 =
            let uu____16050 =
              let uu____16055 =
                let uu____16058 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____16058]  in
              [uu____16055]  in
            let uu____16063 =
              let uu____16064 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16064 tt  in
            (uu____16050, [bb], uu____16063)  in
          FStar_SMTEncoding_Util.mkForall uu____16039  in
        (uu____16038, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16031  in
    let uu____16085 =
      let uu____16088 =
        let uu____16089 =
          let uu____16096 =
            let uu____16097 =
              let uu____16108 =
                let uu____16109 =
                  let uu____16114 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____16114)  in
                FStar_SMTEncoding_Util.mkImp uu____16109  in
              ([[typing_pred]], [xx], uu____16108)  in
            mkForall_fuel uu____16097  in
          (uu____16096, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16089  in
      [uu____16088]  in
    uu____16030 :: uu____16085  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____16170 =
        let uu____16171 =
          let uu____16178 =
            let uu____16181 =
              let uu____16184 =
                let uu____16187 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____16188 =
                  let uu____16191 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____16191]  in
                uu____16187 :: uu____16188  in
              tt :: uu____16184  in
            tt :: uu____16181  in
          ("Prims.Precedes", uu____16178)  in
        FStar_SMTEncoding_Util.mkApp uu____16171  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16170  in
    let precedes_y_x =
      let uu____16195 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16195  in
    let uu____16198 =
      let uu____16199 =
        let uu____16206 =
          let uu____16207 =
            let uu____16218 =
              let uu____16223 =
                let uu____16226 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____16226]  in
              [uu____16223]  in
            let uu____16231 =
              let uu____16232 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16232 tt  in
            (uu____16218, [bb], uu____16231)  in
          FStar_SMTEncoding_Util.mkForall uu____16207  in
        (uu____16206, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16199  in
    let uu____16253 =
      let uu____16256 =
        let uu____16257 =
          let uu____16264 =
            let uu____16265 =
              let uu____16276 =
                let uu____16277 =
                  let uu____16282 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____16282)  in
                FStar_SMTEncoding_Util.mkImp uu____16277  in
              ([[typing_pred]], [xx], uu____16276)  in
            mkForall_fuel uu____16265  in
          (uu____16264, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16257  in
      let uu____16307 =
        let uu____16310 =
          let uu____16311 =
            let uu____16318 =
              let uu____16319 =
                let uu____16330 =
                  let uu____16331 =
                    let uu____16336 =
                      let uu____16337 =
                        let uu____16340 =
                          let uu____16343 =
                            let uu____16346 =
                              let uu____16347 =
                                let uu____16352 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____16353 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____16352, uu____16353)  in
                              FStar_SMTEncoding_Util.mkGT uu____16347  in
                            let uu____16354 =
                              let uu____16357 =
                                let uu____16358 =
                                  let uu____16363 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____16364 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____16363, uu____16364)  in
                                FStar_SMTEncoding_Util.mkGTE uu____16358  in
                              let uu____16365 =
                                let uu____16368 =
                                  let uu____16369 =
                                    let uu____16374 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____16375 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____16374, uu____16375)  in
                                  FStar_SMTEncoding_Util.mkLT uu____16369  in
                                [uu____16368]  in
                              uu____16357 :: uu____16365  in
                            uu____16346 :: uu____16354  in
                          typing_pred_y :: uu____16343  in
                        typing_pred :: uu____16340  in
                      FStar_SMTEncoding_Util.mk_and_l uu____16337  in
                    (uu____16336, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____16331  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____16330)
                 in
              mkForall_fuel uu____16319  in
            (uu____16318,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____16311  in
        [uu____16310]  in
      uu____16256 :: uu____16307  in
    uu____16198 :: uu____16253  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16427 =
      let uu____16428 =
        let uu____16435 =
          let uu____16436 =
            let uu____16447 =
              let uu____16452 =
                let uu____16455 = FStar_SMTEncoding_Term.boxString b  in
                [uu____16455]  in
              [uu____16452]  in
            let uu____16460 =
              let uu____16461 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16461 tt  in
            (uu____16447, [bb], uu____16460)  in
          FStar_SMTEncoding_Util.mkForall uu____16436  in
        (uu____16435, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16428  in
    let uu____16482 =
      let uu____16485 =
        let uu____16486 =
          let uu____16493 =
            let uu____16494 =
              let uu____16505 =
                let uu____16506 =
                  let uu____16511 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____16511)  in
                FStar_SMTEncoding_Util.mkImp uu____16506  in
              ([[typing_pred]], [xx], uu____16505)  in
            mkForall_fuel uu____16494  in
          (uu____16493, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16486  in
      [uu____16485]  in
    uu____16427 :: uu____16482  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____16576 =
      let uu____16577 =
        let uu____16584 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____16584, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16577  in
    [uu____16576]  in
  let mk_and_interp env conj uu____16602 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16627 =
      let uu____16628 =
        let uu____16635 =
          let uu____16636 =
            let uu____16647 =
              let uu____16648 =
                let uu____16653 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16653, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16648  in
            ([[l_and_a_b]], [aa; bb], uu____16647)  in
          FStar_SMTEncoding_Util.mkForall uu____16636  in
        (uu____16635, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16628  in
    [uu____16627]  in
  let mk_or_interp env disj uu____16697 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16722 =
      let uu____16723 =
        let uu____16730 =
          let uu____16731 =
            let uu____16742 =
              let uu____16743 =
                let uu____16748 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16748, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16743  in
            ([[l_or_a_b]], [aa; bb], uu____16742)  in
          FStar_SMTEncoding_Util.mkForall uu____16731  in
        (uu____16730, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16723  in
    [uu____16722]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16817 =
      let uu____16818 =
        let uu____16825 =
          let uu____16826 =
            let uu____16837 =
              let uu____16838 =
                let uu____16843 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16843, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16838  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16837)  in
          FStar_SMTEncoding_Util.mkForall uu____16826  in
        (uu____16825, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16818  in
    [uu____16817]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____16922 =
      let uu____16923 =
        let uu____16930 =
          let uu____16931 =
            let uu____16942 =
              let uu____16943 =
                let uu____16948 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16948, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16943  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16942)  in
          FStar_SMTEncoding_Util.mkForall uu____16931  in
        (uu____16930, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16923  in
    [uu____16922]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____17025 =
      let uu____17026 =
        let uu____17033 =
          let uu____17034 =
            let uu____17045 =
              let uu____17046 =
                let uu____17051 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____17051, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17046  in
            ([[l_imp_a_b]], [aa; bb], uu____17045)  in
          FStar_SMTEncoding_Util.mkForall uu____17034  in
        (uu____17033, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17026  in
    [uu____17025]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____17120 =
      let uu____17121 =
        let uu____17128 =
          let uu____17129 =
            let uu____17140 =
              let uu____17141 =
                let uu____17146 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____17146, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17141  in
            ([[l_iff_a_b]], [aa; bb], uu____17140)  in
          FStar_SMTEncoding_Util.mkForall uu____17129  in
        (uu____17128, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17121  in
    [uu____17120]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____17204 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____17204  in
    let uu____17207 =
      let uu____17208 =
        let uu____17215 =
          let uu____17216 =
            let uu____17227 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____17227)  in
          FStar_SMTEncoding_Util.mkForall uu____17216  in
        (uu____17215, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17208  in
    [uu____17207]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____17293 =
        let uu____17300 =
          let uu____17303 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17303]  in
        ("Valid", uu____17300)  in
      FStar_SMTEncoding_Util.mkApp uu____17293  in
    let uu____17306 =
      let uu____17307 =
        let uu____17314 =
          let uu____17315 =
            let uu____17326 =
              let uu____17327 =
                let uu____17332 =
                  let uu____17333 =
                    let uu____17344 =
                      let uu____17349 =
                        let uu____17352 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17352]  in
                      [uu____17349]  in
                    let uu____17357 =
                      let uu____17358 =
                        let uu____17363 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17363, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17358  in
                    (uu____17344, [xx1], uu____17357)  in
                  FStar_SMTEncoding_Util.mkForall uu____17333  in
                (uu____17332, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17327  in
            ([[l_forall_a_b]], [aa; bb], uu____17326)  in
          FStar_SMTEncoding_Util.mkForall uu____17315  in
        (uu____17314, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17307  in
    [uu____17306]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____17451 =
        let uu____17458 =
          let uu____17461 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17461]  in
        ("Valid", uu____17458)  in
      FStar_SMTEncoding_Util.mkApp uu____17451  in
    let uu____17464 =
      let uu____17465 =
        let uu____17472 =
          let uu____17473 =
            let uu____17484 =
              let uu____17485 =
                let uu____17490 =
                  let uu____17491 =
                    let uu____17502 =
                      let uu____17507 =
                        let uu____17510 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17510]  in
                      [uu____17507]  in
                    let uu____17515 =
                      let uu____17516 =
                        let uu____17521 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17521, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17516  in
                    (uu____17502, [xx1], uu____17515)  in
                  FStar_SMTEncoding_Util.mkExists uu____17491  in
                (uu____17490, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17485  in
            ([[l_exists_a_b]], [aa; bb], uu____17484)  in
          FStar_SMTEncoding_Util.mkForall uu____17473  in
        (uu____17472, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17465  in
    [uu____17464]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____17587 =
      let uu____17588 =
        let uu____17595 =
          let uu____17596 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____17596 range_ty  in
        let uu____17597 = varops.mk_unique "typing_range_const"  in
        (uu____17595, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____17597)
         in
      FStar_SMTEncoding_Util.mkAssume uu____17588  in
    [uu____17587]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____17637 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17637 x1 t  in
      let uu____17638 =
        let uu____17649 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____17649)  in
      FStar_SMTEncoding_Util.mkForall uu____17638  in
    let uu____17672 =
      let uu____17673 =
        let uu____17680 =
          let uu____17681 =
            let uu____17692 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____17692)  in
          FStar_SMTEncoding_Util.mkForall uu____17681  in
        (uu____17680,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17673  in
    [uu____17672]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17748 =
      let uu____17749 =
        let uu____17756 =
          let uu____17757 =
            let uu____17772 =
              let uu____17773 =
                let uu____17778 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17779 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17778, uu____17779)  in
              FStar_SMTEncoding_Util.mkAnd uu____17773  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17772)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17757  in
        (uu____17756,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17749  in
    [uu____17748]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____18239 =
            FStar_Util.find_opt
              (fun uu____18271  ->
                 match uu____18271 with
                 | (l,uu____18283) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____18239 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____18317,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____18368 = encode_function_type_as_formula t env  in
        match uu____18368 with
        | (form,decls) ->
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
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____18420 =
                ((let uu____18423 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____18423) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____18420
              then
                let arg_sorts =
                  let uu____18433 =
                    let uu____18434 = FStar_Syntax_Subst.compress t_norm  in
                    uu____18434.FStar_Syntax_Syntax.n  in
                  match uu____18433 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____18440) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____18470  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____18475 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____18477 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____18477 with
                | (vname,vtok,env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    ([d; dd], env1)
              else
                (let uu____18510 = prims.is lid  in
                 if uu____18510
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____18518 = prims.mk lid vname  in
                   match uu____18518 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____18545 =
                      let uu____18556 = curried_arrow_formals_comp t_norm  in
                      match uu____18556 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____18574 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____18574
                            then
                              let uu____18575 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___121_18578 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___121_18578.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___121_18578.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___121_18578.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___121_18578.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___121_18578.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___121_18578.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___121_18578.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___121_18578.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___121_18578.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___121_18578.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___121_18578.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___121_18578.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___121_18578.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___121_18578.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___121_18578.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___121_18578.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___121_18578.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___121_18578.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___121_18578.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___121_18578.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___121_18578.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___121_18578.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___121_18578.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___121_18578.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___121_18578.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___121_18578.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___121_18578.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___121_18578.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___121_18578.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___121_18578.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___121_18578.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___121_18578.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___121_18578.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___121_18578.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___121_18578.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___121_18578.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____18575
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____18590 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____18590)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____18545 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____18640 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____18640 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____18665 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___93_18715  ->
                                       match uu___93_18715 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____18719 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18719 with
                                            | (uu____18740,(xxsym,uu____18742))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____18760 =
                                                  let uu____18761 =
                                                    let uu____18768 =
                                                      let uu____18769 =
                                                        let uu____18780 =
                                                          let uu____18781 =
                                                            let uu____18786 =
                                                              let uu____18787
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____18787
                                                               in
                                                            (vapp,
                                                              uu____18786)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____18781
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18780)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18769
                                                       in
                                                    (uu____18768,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18761
                                                   in
                                                [uu____18760])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____18806 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18806 with
                                            | (uu____18827,(xxsym,uu____18829))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  }  in
                                                let tp_name =
                                                  mk_term_projector_name d f1
                                                   in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx])
                                                   in
                                                let uu____18852 =
                                                  let uu____18853 =
                                                    let uu____18860 =
                                                      let uu____18861 =
                                                        let uu____18872 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18872)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18861
                                                       in
                                                    (uu____18860,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18853
                                                   in
                                                [uu____18852])
                                       | uu____18889 -> []))
                                in
                             let uu____18890 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____18890 with
                              | (vars,guards,env',decls1,uu____18917) ->
                                  let uu____18930 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18939 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18939, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18941 =
                                          encode_formula p env'  in
                                        (match uu____18941 with
                                         | (g,ds) ->
                                             let uu____18952 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____18952,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18930 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____18965 =
                                           let uu____18972 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____18972)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____18965
                                          in
                                       let uu____18981 =
                                         let vname_decl =
                                           let uu____18989 =
                                             let uu____19000 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____19010  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____19000,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____18989
                                            in
                                         let uu____19019 =
                                           let env2 =
                                             let uu___122_19025 = env1  in
                                             {
                                               bindings =
                                                 (uu___122_19025.bindings);
                                               depth = (uu___122_19025.depth);
                                               tcenv = (uu___122_19025.tcenv);
                                               warn = (uu___122_19025.warn);
                                               cache = (uu___122_19025.cache);
                                               nolabels =
                                                 (uu___122_19025.nolabels);
                                               use_zfuel_name =
                                                 (uu___122_19025.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___122_19025.current_module_name)
                                             }  in
                                           let uu____19026 =
                                             let uu____19027 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____19027
                                              in
                                           if uu____19026
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____19019 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____19042::uu____19043 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                      in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff
                                                      in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff]
                                                      in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)]
                                                      in
                                                   let guarded_tok_typing =
                                                     let uu____19083 =
                                                       let uu____19094 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____19094)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____19083
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____19121 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____19124 =
                                               match formals with
                                               | [] ->
                                                   let uu____19141 =
                                                     let uu____19142 =
                                                       let uu____19145 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____19145
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____19142
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____19141)
                                               | uu____19154 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____19161 =
                                                       let uu____19168 =
                                                         let uu____19169 =
                                                           let uu____19180 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____19180)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____19169
                                                          in
                                                       (uu____19168,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____19161
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____19124 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____18981 with
                                        | (decls2,env2) ->
                                            let uu____19223 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____19231 =
                                                encode_term res_t1 env'  in
                                              match uu____19231 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____19244 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____19244, decls)
                                               in
                                            (match uu____19223 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____19255 =
                                                     let uu____19262 =
                                                       let uu____19263 =
                                                         let uu____19274 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____19274)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____19263
                                                        in
                                                     (uu____19262,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____19255
                                                    in
                                                 let freshness =
                                                   let uu____19290 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____19290
                                                   then
                                                     let uu____19295 =
                                                       let uu____19296 =
                                                         let uu____19307 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____19318 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____19307,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____19318)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____19296
                                                        in
                                                     let uu____19321 =
                                                       let uu____19324 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____19324]  in
                                                     uu____19295 ::
                                                       uu____19321
                                                   else []  in
                                                 let g =
                                                   let uu____19329 =
                                                     let uu____19332 =
                                                       let uu____19335 =
                                                         let uu____19338 =
                                                           let uu____19341 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____19341
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____19338
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____19335
                                                        in
                                                     FStar_List.append decls2
                                                       uu____19332
                                                      in
                                                   FStar_List.append decls11
                                                     uu____19329
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (fvar_binding,FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____19374 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19374 with
          | FStar_Pervasives_Native.None  ->
              let uu____19385 = encode_free_var false env x t t_norm []  in
              (match uu____19385 with
               | (decls,env1) ->
                   let fvb =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
  
let (encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t  in
            let uu____19448 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____19448 with
            | (decls,env1) ->
                let uu____19467 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____19467
                then
                  let uu____19474 =
                    let uu____19477 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____19477  in
                  (uu____19474, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____19535  ->
                fun lb  ->
                  match uu____19535 with
                  | (decls,env1) ->
                      let uu____19555 =
                        let uu____19562 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____19562
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____19555 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____19585 = FStar_Syntax_Util.head_and_args t  in
    match uu____19585 with
    | (hd1,args) ->
        let uu____19622 =
          let uu____19623 = FStar_Syntax_Util.un_uinst hd1  in
          uu____19623.FStar_Syntax_Syntax.n  in
        (match uu____19622 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____19627,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____19646 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____19674  ->
      fun quals  ->
        match uu____19674 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____19758 = FStar_Util.first_N nbinders formals  in
              match uu____19758 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19839  ->
                         fun uu____19840  ->
                           match (uu____19839, uu____19840) with
                           | ((formal,uu____19858),(binder,uu____19860)) ->
                               let uu____19869 =
                                 let uu____19876 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19876)  in
                               FStar_Syntax_Syntax.NT uu____19869) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19884 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19915  ->
                              match uu____19915 with
                              | (x,i) ->
                                  let uu____19926 =
                                    let uu___123_19927 = x  in
                                    let uu____19928 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___123_19927.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___123_19927.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19928
                                    }  in
                                  (uu____19926, i)))
                       in
                    FStar_All.pipe_right uu____19884
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19946 =
                      let uu____19951 = FStar_Syntax_Subst.compress body  in
                      let uu____19952 =
                        let uu____19953 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____19953
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____19951
                        uu____19952
                       in
                    uu____19946 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____20022 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____20022
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___124_20025 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___124_20025.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___124_20025.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___124_20025.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___124_20025.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___124_20025.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___124_20025.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___124_20025.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___124_20025.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___124_20025.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___124_20025.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___124_20025.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___124_20025.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___124_20025.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___124_20025.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___124_20025.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___124_20025.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___124_20025.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___124_20025.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___124_20025.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___124_20025.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___124_20025.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___124_20025.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___124_20025.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___124_20025.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___124_20025.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___124_20025.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___124_20025.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___124_20025.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___124_20025.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___124_20025.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___124_20025.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___124_20025.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___124_20025.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___124_20025.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___124_20025.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___124_20025.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____20062 = FStar_Syntax_Util.abs_formals e  in
                match uu____20062 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____20126::uu____20127 ->
                         let uu____20142 =
                           let uu____20143 =
                             let uu____20146 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____20146
                              in
                           uu____20143.FStar_Syntax_Syntax.n  in
                         (match uu____20142 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____20189 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____20189 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____20231 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____20231
                                   then
                                     let uu____20266 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____20266 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____20360  ->
                                                   fun uu____20361  ->
                                                     match (uu____20360,
                                                             uu____20361)
                                                     with
                                                     | ((x,uu____20379),
                                                        (b,uu____20381)) ->
                                                         let uu____20390 =
                                                           let uu____20397 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____20397)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____20390)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____20399 =
                                            let uu____20420 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____20420)
                                             in
                                          (uu____20399, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____20488 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____20488 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____20577) ->
                              let uu____20582 =
                                let uu____20603 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____20603  in
                              (uu____20582, true)
                          | uu____20668 when Prims.op_Negation norm1 ->
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
                                  env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____20670 ->
                              let uu____20671 =
                                let uu____20672 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____20673 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____20672
                                  uu____20673
                                 in
                              failwith uu____20671)
                     | uu____20698 ->
                         let rec aux' t_norm2 =
                           let uu____20725 =
                             let uu____20726 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____20726.FStar_Syntax_Syntax.n  in
                           match uu____20725 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____20767 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____20767 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____20795 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____20795 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20875)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20880 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20936 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20936
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20948 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____21011  ->
                            fun lb  ->
                              match uu____21011 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____21066 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____21066
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____21069 =
                                      let uu____21078 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____21078
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____21069 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____20948 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____21203 =
                          if fvb.smt_arity = (Prims.parse_int "0")
                          then
                            FStar_SMTEncoding_Util.mkFreeV
                              ((fvb.smt_id),
                                FStar_SMTEncoding_Term.Term_sort)
                          else
                            raise_arity_mismatch fvb.smt_id fvb.smt_arity
                              (Prims.parse_int "0") rng
                           in
                        match vars with
                        | [] -> mk_fv ()
                        | uu____21209 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____21217 = mk_fv ()  in
                                   mk_Apply uu____21217 vars)
                            else
                              (let uu____21219 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____21219)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____21279;
                             FStar_Syntax_Syntax.lbeff = uu____21280;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____21282;
                             FStar_Syntax_Syntax.lbpos = uu____21283;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____21307 =
                              let uu____21314 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____21314 with
                              | (tcenv',uu____21332,e_t) ->
                                  let uu____21338 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____21349 -> failwith "Impossible"
                                     in
                                  (match uu____21338 with
                                   | (e1,t_norm1) ->
                                       ((let uu___127_21365 = env2  in
                                         {
                                           bindings =
                                             (uu___127_21365.bindings);
                                           depth = (uu___127_21365.depth);
                                           tcenv = tcenv';
                                           warn = (uu___127_21365.warn);
                                           cache = (uu___127_21365.cache);
                                           nolabels =
                                             (uu___127_21365.nolabels);
                                           use_zfuel_name =
                                             (uu___127_21365.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___127_21365.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___127_21365.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____21307 with
                             | (env',e1,t_norm1) ->
                                 let uu____21375 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____21375 with
                                  | ((binders,body,uu____21396,t_body),curry)
                                      ->
                                      ((let uu____21408 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____21408
                                        then
                                          let uu____21409 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____21410 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____21409 uu____21410
                                        else ());
                                       (let uu____21412 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____21412 with
                                        | (vars,guards,env'1,binder_decls,uu____21439)
                                            ->
                                            let body1 =
                                              let uu____21453 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____21453
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None)
                                               in
                                            let app =
                                              let uu____21470 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____21470 curry fvb
                                                vars
                                               in
                                            let uu____21471 =
                                              let uu____21480 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____21480
                                              then
                                                let uu____21491 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____21492 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____21491, uu____21492)
                                              else
                                                (let uu____21502 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____21502))
                                               in
                                            (match uu____21471 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____21525 =
                                                     let uu____21532 =
                                                       let uu____21533 =
                                                         let uu____21544 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____21544)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____21533
                                                        in
                                                     let uu____21555 =
                                                       let uu____21558 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21558
                                                        in
                                                     (uu____21532,
                                                       uu____21555,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____21525
                                                    in
                                                 let uu____21561 =
                                                   let uu____21564 =
                                                     let uu____21567 =
                                                       let uu____21570 =
                                                         let uu____21573 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____21573
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____21570
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____21567
                                                      in
                                                   FStar_List.append decls1
                                                     uu____21564
                                                    in
                                                 (uu____21561, env2))))))
                        | uu____21578 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____21641 = varops.fresh "fuel"  in
                          (uu____21641, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21644 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____21691  ->
                                  fun fvb  ->
                                    match uu____21691 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____21737 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21737  in
                                        let gtok =
                                          let uu____21739 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21739  in
                                        let env4 =
                                          let uu____21741 =
                                            let uu____21744 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____21744
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____21741
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____21644 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21852 t_norm
                              uu____21854 =
                              match (uu____21852, uu____21854) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____21884;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____21885;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____21887;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____21888;_})
                                  ->
                                  let uu____21909 =
                                    let uu____21916 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21916 with
                                    | (tcenv',uu____21938,e_t) ->
                                        let uu____21944 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21955 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21944 with
                                         | (e1,t_norm1) ->
                                             ((let uu___128_21971 = env3  in
                                               {
                                                 bindings =
                                                   (uu___128_21971.bindings);
                                                 depth =
                                                   (uu___128_21971.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___128_21971.warn);
                                                 cache =
                                                   (uu___128_21971.cache);
                                                 nolabels =
                                                   (uu___128_21971.nolabels);
                                                 use_zfuel_name =
                                                   (uu___128_21971.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___128_21971.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___128_21971.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21909 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21986 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21986
                                         then
                                           let uu____21987 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21988 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21989 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21987 uu____21988
                                             uu____21989
                                         else ());
                                        (let uu____21991 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____21991 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____22028 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____22028
                                               then
                                                 let uu____22029 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____22030 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____22031 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____22032 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____22029 uu____22030
                                                   uu____22031 uu____22032
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____22036 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____22036 with
                                               | (vars,guards,env'1,binder_decls,uu____22067)
                                                   ->
                                                   let decl_g =
                                                     let uu____22081 =
                                                       let uu____22092 =
                                                         let uu____22095 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____22095
                                                          in
                                                       (g, uu____22092,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____22081
                                                      in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       fvb.fvar_lid g
                                                      in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications"))
                                                      in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars
                                                      in
                                                   let app =
                                                     let uu____22120 =
                                                       let uu____22127 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____22127)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22120
                                                      in
                                                   let gsapp =
                                                     let uu____22137 =
                                                       let uu____22144 =
                                                         let uu____22147 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____22147 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22144)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22137
                                                      in
                                                   let gmax =
                                                     let uu____22153 =
                                                       let uu____22160 =
                                                         let uu____22163 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____22163 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22160)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22153
                                                      in
                                                   let body1 =
                                                     let uu____22169 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____22169
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____22171 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____22171 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____22189 =
                                                            let uu____22196 =
                                                              let uu____22197
                                                                =
                                                                let uu____22212
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____22212)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____22197
                                                               in
                                                            let uu____22233 =
                                                              let uu____22236
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____22236
                                                               in
                                                            (uu____22196,
                                                              uu____22233,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22189
                                                           in
                                                        let eqn_f =
                                                          let uu____22240 =
                                                            let uu____22247 =
                                                              let uu____22248
                                                                =
                                                                let uu____22259
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____22259)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22248
                                                               in
                                                            (uu____22247,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22240
                                                           in
                                                        let eqn_g' =
                                                          let uu____22273 =
                                                            let uu____22280 =
                                                              let uu____22281
                                                                =
                                                                let uu____22292
                                                                  =
                                                                  let uu____22293
                                                                    =
                                                                    let uu____22298
                                                                    =
                                                                    let uu____22299
                                                                    =
                                                                    let uu____22306
                                                                    =
                                                                    let uu____22309
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____22309
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____22306)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____22299
                                                                     in
                                                                    (gsapp,
                                                                    uu____22298)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____22293
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____22292)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22281
                                                               in
                                                            (uu____22280,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22273
                                                           in
                                                        let uu____22332 =
                                                          let uu____22341 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____22341
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____22370)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____22395
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____22395
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____22400
                                                                  =
                                                                  let uu____22407
                                                                    =
                                                                    let uu____22408
                                                                    =
                                                                    let uu____22419
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22419)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22408
                                                                     in
                                                                  (uu____22407,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____22400
                                                                 in
                                                              let uu____22440
                                                                =
                                                                let uu____22447
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____22447
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____22460
                                                                    =
                                                                    let uu____22463
                                                                    =
                                                                    let uu____22464
                                                                    =
                                                                    let uu____22471
                                                                    =
                                                                    let uu____22472
                                                                    =
                                                                    let uu____22483
                                                                    =
                                                                    let uu____22484
                                                                    =
                                                                    let uu____22489
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____22489,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____22484
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22483)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22472
                                                                     in
                                                                    (uu____22471,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____22464
                                                                     in
                                                                    [uu____22463]
                                                                     in
                                                                    (d3,
                                                                    uu____22460)
                                                                 in
                                                              (match uu____22440
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____22332
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
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
                                                               env02))))))))
                               in
                            let uu____22554 =
                              let uu____22567 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22628  ->
                                   fun uu____22629  ->
                                     match (uu____22628, uu____22629) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22754 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22754 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22567
                               in
                            (match uu____22554 with
                             | (decls2,eqns,env01) ->
                                 let uu____22827 =
                                   let isDeclFun uu___94_22841 =
                                     match uu___94_22841 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22842 -> true
                                     | uu____22853 -> false  in
                                   let uu____22854 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22854
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22827 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22894 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___95_22898  ->
                                 match uu___95_22898 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22899 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22905 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22905)))
                         in
                      if uu____22894
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks_fvbs
                               env1
                           else
                             encode_rec_lbdefs bindings typs1 toks_fvbs env1
                         with | Inner_let_rec  -> (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22957 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22957
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____23018 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____23018 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____23022 = encode_sigelt' env se  in
      match uu____23022 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____23038 =
                  let uu____23039 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____23039  in
                [uu____23038]
            | uu____23040 ->
                let uu____23041 =
                  let uu____23044 =
                    let uu____23045 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____23045  in
                  uu____23044 :: g  in
                let uu____23046 =
                  let uu____23049 =
                    let uu____23050 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____23050  in
                  [uu____23049]  in
                FStar_List.append uu____23041 uu____23046
             in
          (g1, env1)

and (encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____23065 =
          let uu____23066 = FStar_Syntax_Subst.compress t  in
          uu____23066.FStar_Syntax_Syntax.n  in
        match uu____23065 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____23070)) -> s = "opaque_to_smt"
        | uu____23071 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____23078 =
          let uu____23079 = FStar_Syntax_Subst.compress t  in
          uu____23079.FStar_Syntax_Syntax.n  in
        match uu____23078 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____23083)) -> s = "uninterpreted_by_smt"
        | uu____23084 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23089 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____23094 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____23105 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____23108 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____23111 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____23126 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23130 =
            let uu____23131 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____23131 Prims.op_Negation  in
          if uu____23130
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____23159 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____23183 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____23183 with
               | (formals,uu____23201) ->
                   let arity = FStar_List.length formals  in
                   let uu____23219 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____23219 with
                    | (aname,atok,env2) ->
                        let uu____23239 =
                          let uu____23244 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____23244 env2  in
                        (match uu____23239 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____23256 =
                                 let uu____23257 =
                                   let uu____23268 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____23284  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____23268,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____23257
                                  in
                               [uu____23256;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____23297 =
                               let aux uu____23353 uu____23354 =
                                 match (uu____23353, uu____23354) with
                                 | ((bv,uu____23406),(env3,acc_sorts,acc)) ->
                                     let uu____23444 = gen_term_var env3 bv
                                        in
                                     (match uu____23444 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____23297 with
                              | (uu____23516,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____23539 =
                                      let uu____23546 =
                                        let uu____23547 =
                                          let uu____23558 =
                                            let uu____23559 =
                                              let uu____23564 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____23564)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23559
                                             in
                                          ([[app]], xs_sorts, uu____23558)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23547
                                         in
                                      (uu____23546,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23539
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23584 =
                                      let uu____23591 =
                                        let uu____23592 =
                                          let uu____23603 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23603)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23592
                                         in
                                      (uu____23591,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23584
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23622 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23622 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23650,uu____23651)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23652 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____23652 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23669,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23675 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___96_23679  ->
                      match uu___96_23679 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23680 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23685 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23686 -> false))
               in
            Prims.op_Negation uu____23675  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23695 =
               let uu____23702 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23702 env fv t quals  in
             match uu____23695 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23717 =
                   let uu____23720 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23720  in
                 (uu____23717, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23728 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23728 with
           | (uu____23737,f1) ->
               let uu____23739 = encode_formula f1 env  in
               (match uu____23739 with
                | (f2,decls) ->
                    let g =
                      let uu____23753 =
                        let uu____23754 =
                          let uu____23761 =
                            let uu____23764 =
                              let uu____23765 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23765
                               in
                            FStar_Pervasives_Native.Some uu____23764  in
                          let uu____23766 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23761, uu____23766)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23754  in
                      [uu____23753]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23772) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23784 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23802 =
                       let uu____23805 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23805.FStar_Syntax_Syntax.fv_name  in
                     uu____23802.FStar_Syntax_Syntax.v  in
                   let uu____23806 =
                     let uu____23807 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23807  in
                   if uu____23806
                   then
                     let val_decl =
                       let uu___131_23835 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___131_23835.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___131_23835.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___131_23835.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23840 = encode_sigelt' env1 val_decl  in
                     match uu____23840 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23784 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23868,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23870;
                          FStar_Syntax_Syntax.lbtyp = uu____23871;
                          FStar_Syntax_Syntax.lbeff = uu____23872;
                          FStar_Syntax_Syntax.lbdef = uu____23873;
                          FStar_Syntax_Syntax.lbattrs = uu____23874;
                          FStar_Syntax_Syntax.lbpos = uu____23875;_}::[]),uu____23876)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23899 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____23899 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23928 =
                   let uu____23931 =
                     let uu____23932 =
                       let uu____23939 =
                         let uu____23940 =
                           let uu____23951 =
                             let uu____23952 =
                               let uu____23957 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23957)  in
                             FStar_SMTEncoding_Util.mkEq uu____23952  in
                           ([[b2t_x]], [xx], uu____23951)  in
                         FStar_SMTEncoding_Util.mkForall uu____23940  in
                       (uu____23939,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23932  in
                   [uu____23931]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23928
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23990,uu____23991) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_24000  ->
                  match uu___97_24000 with
                  | FStar_Syntax_Syntax.Discriminator uu____24001 -> true
                  | uu____24002 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____24005,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____24016 =
                     let uu____24017 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____24017.FStar_Ident.idText  in
                   uu____24016 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___98_24021  ->
                     match uu___98_24021 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____24022 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____24026) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___99_24043  ->
                  match uu___99_24043 with
                  | FStar_Syntax_Syntax.Projector uu____24044 -> true
                  | uu____24049 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____24052 = try_lookup_free_var env l  in
          (match uu____24052 with
           | FStar_Pervasives_Native.Some uu____24059 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___132_24063 = se  in
                 let uu____24064 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____24064;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___132_24063.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___132_24063.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___132_24063.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____24071) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____24089) ->
          let uu____24098 = encode_sigelts env ses  in
          (match uu____24098 with
           | (g,env1) ->
               let uu____24115 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___100_24138  ->
                         match uu___100_24138 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____24139;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____24140;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____24141;_}
                             -> false
                         | uu____24144 -> true))
                  in
               (match uu____24115 with
                | (g',inversions) ->
                    let uu____24159 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___101_24180  ->
                              match uu___101_24180 with
                              | FStar_SMTEncoding_Term.DeclFun uu____24181 ->
                                  true
                              | uu____24192 -> false))
                       in
                    (match uu____24159 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____24210,tps,k,uu____24213,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___102_24230  ->
                    match uu___102_24230 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____24231 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____24242 = c  in
              match uu____24242 with
              | (name,args,uu____24247,uu____24248,uu____24249) ->
                  let uu____24254 =
                    let uu____24255 =
                      let uu____24266 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____24283  ->
                                match uu____24283 with
                                | (uu____24290,sort,uu____24292) -> sort))
                         in
                      (name, uu____24266, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____24255  in
                  [uu____24254]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____24323 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____24329 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____24329 FStar_Option.isNone))
               in
            if uu____24323
            then []
            else
              (let uu____24361 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____24361 with
               | (xxsym,xx) ->
                   let uu____24370 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____24409  ->
                             fun l  ->
                               match uu____24409 with
                               | (out,decls) ->
                                   let uu____24429 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____24429 with
                                    | (uu____24440,data_t) ->
                                        let uu____24442 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____24442 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____24488 =
                                                 let uu____24489 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____24489.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____24488 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____24500,indices) ->
                                                   indices
                                               | uu____24522 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24546  ->
                                                         match uu____24546
                                                         with
                                                         | (x,uu____24552) ->
                                                             let uu____24553
                                                               =
                                                               let uu____24554
                                                                 =
                                                                 let uu____24561
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____24561,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24554
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____24553)
                                                    env)
                                                in
                                             let uu____24564 =
                                               encode_args indices env1  in
                                             (match uu____24564 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____24590 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____24606
                                                                 =
                                                                 let uu____24611
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____24611,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____24606)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____24590
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____24614 =
                                                      let uu____24615 =
                                                        let uu____24620 =
                                                          let uu____24621 =
                                                            let uu____24626 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____24626,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____24621
                                                           in
                                                        (out, uu____24620)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____24615
                                                       in
                                                    (uu____24614,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____24370 with
                    | (data_ax,decls) ->
                        let uu____24639 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____24639 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24650 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24650 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____24654 =
                                 let uu____24661 =
                                   let uu____24662 =
                                     let uu____24673 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24688 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24673,
                                       uu____24688)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24662
                                    in
                                 let uu____24703 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____24661,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24703)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____24654
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24706 =
            let uu____24719 =
              let uu____24720 = FStar_Syntax_Subst.compress k  in
              uu____24720.FStar_Syntax_Syntax.n  in
            match uu____24719 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24765 -> (tps, k)  in
          (match uu____24706 with
           | (formals,res) ->
               let uu____24788 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24788 with
                | (formals1,res1) ->
                    let uu____24799 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24799 with
                     | (vars,guards,env',binder_decls,uu____24824) ->
                         let arity = FStar_List.length vars  in
                         let uu____24838 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____24838 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24861 =
                                  let uu____24868 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24868)  in
                                FStar_SMTEncoding_Util.mkApp uu____24861  in
                              let uu____24877 =
                                let tname_decl =
                                  let uu____24887 =
                                    let uu____24888 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24920  ->
                                              match uu____24920 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24933 = varops.next_id ()  in
                                    (tname, uu____24888,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24933, false)
                                     in
                                  constructor_or_logic_type_decl uu____24887
                                   in
                                let uu____24942 =
                                  match vars with
                                  | [] ->
                                      let uu____24955 =
                                        let uu____24956 =
                                          let uu____24959 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____24959
                                           in
                                        push_free_var env1 t arity tname
                                          uu____24956
                                         in
                                      ([], uu____24955)
                                  | uu____24970 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24979 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24979
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24993 =
                                          let uu____25000 =
                                            let uu____25001 =
                                              let uu____25016 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____25016)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____25001
                                             in
                                          (uu____25000,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24993
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24942 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24877 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____25056 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____25056 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____25074 =
                                               let uu____25075 =
                                                 let uu____25082 =
                                                   let uu____25083 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____25083
                                                    in
                                                 (uu____25082,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____25075
                                                in
                                             [uu____25074]
                                           else []  in
                                         let uu____25087 =
                                           let uu____25090 =
                                             let uu____25093 =
                                               let uu____25094 =
                                                 let uu____25101 =
                                                   let uu____25102 =
                                                     let uu____25113 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____25113)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____25102
                                                    in
                                                 (uu____25101,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____25094
                                                in
                                             [uu____25093]  in
                                           FStar_List.append karr uu____25090
                                            in
                                         FStar_List.append decls1 uu____25087
                                      in
                                   let aux =
                                     let uu____25129 =
                                       let uu____25132 =
                                         inversion_axioms tapp vars  in
                                       let uu____25135 =
                                         let uu____25138 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____25138]  in
                                       FStar_List.append uu____25132
                                         uu____25135
                                        in
                                     FStar_List.append kindingAx uu____25129
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____25145,uu____25146,uu____25147,uu____25148,uu____25149)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____25157,t,uu____25159,n_tps,uu____25161) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____25169 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____25169 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____25209 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____25209 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____25230 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____25230 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____25244 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____25244 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____25314 =
                                            mk_term_projector_name d x  in
                                          (uu____25314,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____25316 =
                                  let uu____25335 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____25335, true)
                                   in
                                FStar_All.pipe_right uu____25316
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                 in
                              let app = mk_Apply ddtok_tm vars  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____25374 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____25374 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____25386::uu____25387 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff]  in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____25432 =
                                           let uu____25443 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____25443)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____25432
                                     | uu____25468 -> tok_typing  in
                                   let uu____25477 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____25477 with
                                    | (vars',guards',env'',decls_formals,uu____25502)
                                        ->
                                        let uu____25515 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1
                                           in
                                        (match uu____25515 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25546 ->
                                                   let uu____25553 =
                                                     let uu____25554 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25554
                                                      in
                                                   [uu____25553]
                                                in
                                             let encode_elim uu____25566 =
                                               let uu____25567 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____25567 with
                                               | (head1,args) ->
                                                   let uu____25610 =
                                                     let uu____25611 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____25611.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____25610 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25621;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25622;_},uu____25623)
                                                        ->
                                                        let uu____25628 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25628
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25641
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25641
                                                              with
                                                              | (encoded_args,arg_decls)
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
                                                                    uu____25690
                                                                    ->
                                                                    let uu____25691
                                                                    =
                                                                    let uu____25696
                                                                    =
                                                                    let uu____25697
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25697
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25696)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25691
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25713
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25714
                                                                     in
                                                                    if
                                                                    uu____25713
                                                                    then
                                                                    let uu____25727
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25727]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25729
                                                                    =
                                                                    let uu____25742
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25792
                                                                     ->
                                                                    fun
                                                                    uu____25793
                                                                     ->
                                                                    match 
                                                                    (uu____25792,
                                                                    uu____25793)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25888
                                                                    =
                                                                    let uu____25895
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25895
                                                                     in
                                                                    (match uu____25888
                                                                    with
                                                                    | 
                                                                    (uu____25908,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25916
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25916
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25918
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25918
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____25742
                                                                     in
                                                                  (match uu____25729
                                                                   with
                                                                   | 
                                                                   (uu____25933,arg_vars,elim_eqns_or_guards,uu____25936)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1
                                                                     in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____25964
                                                                    =
                                                                    let uu____25971
                                                                    =
                                                                    let uu____25972
                                                                    =
                                                                    let uu____25983
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25994
                                                                    =
                                                                    let uu____25995
                                                                    =
                                                                    let uu____26000
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26000)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25995
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25983,
                                                                    uu____25994)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25972
                                                                     in
                                                                    (uu____25971,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25964
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26018
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26018
                                                                    then
                                                                    let x =
                                                                    let uu____26024
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26024,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26026
                                                                    =
                                                                    let uu____26033
                                                                    =
                                                                    let uu____26034
                                                                    =
                                                                    let uu____26045
                                                                    =
                                                                    let uu____26050
                                                                    =
                                                                    let uu____26053
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26053]
                                                                     in
                                                                    [uu____26050]
                                                                     in
                                                                    let uu____26058
                                                                    =
                                                                    let uu____26059
                                                                    =
                                                                    let uu____26064
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26065
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26064,
                                                                    uu____26065)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26059
                                                                     in
                                                                    (uu____26045,
                                                                    [x],
                                                                    uu____26058)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26034
                                                                     in
                                                                    let uu____26084
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26033,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26084)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26026
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26091
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____26119
                                                                    =
                                                                    let uu____26120
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26120
                                                                    dapp1  in
                                                                    [uu____26119])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26091
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26127
                                                                    =
                                                                    let uu____26134
                                                                    =
                                                                    let uu____26135
                                                                    =
                                                                    let uu____26146
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26157
                                                                    =
                                                                    let uu____26158
                                                                    =
                                                                    let uu____26163
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26163)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26158
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26146,
                                                                    uu____26157)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26135
                                                                     in
                                                                    (uu____26134,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26127)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____26183 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____26183
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____26196
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____26196
                                                              with
                                                              | (encoded_args,arg_decls)
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
                                                                    uu____26245
                                                                    ->
                                                                    let uu____26246
                                                                    =
                                                                    let uu____26251
                                                                    =
                                                                    let uu____26252
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____26252
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____26251)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____26246
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____26268
                                                                    =
                                                                    let uu____26269
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____26269
                                                                     in
                                                                    if
                                                                    uu____26268
                                                                    then
                                                                    let uu____26282
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____26282]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____26284
                                                                    =
                                                                    let uu____26297
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____26347
                                                                     ->
                                                                    fun
                                                                    uu____26348
                                                                     ->
                                                                    match 
                                                                    (uu____26347,
                                                                    uu____26348)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____26443
                                                                    =
                                                                    let uu____26450
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____26450
                                                                     in
                                                                    (match uu____26443
                                                                    with
                                                                    | 
                                                                    (uu____26463,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____26471
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____26471
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____26473
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____26473
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____26297
                                                                     in
                                                                  (match uu____26284
                                                                   with
                                                                   | 
                                                                   (uu____26488,arg_vars,elim_eqns_or_guards,uu____26491)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1
                                                                     in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____26519
                                                                    =
                                                                    let uu____26526
                                                                    =
                                                                    let uu____26527
                                                                    =
                                                                    let uu____26538
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26549
                                                                    =
                                                                    let uu____26550
                                                                    =
                                                                    let uu____26555
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26555)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26550
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26538,
                                                                    uu____26549)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26527
                                                                     in
                                                                    (uu____26526,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26519
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26573
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26573
                                                                    then
                                                                    let x =
                                                                    let uu____26579
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26579,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26581
                                                                    =
                                                                    let uu____26588
                                                                    =
                                                                    let uu____26589
                                                                    =
                                                                    let uu____26600
                                                                    =
                                                                    let uu____26605
                                                                    =
                                                                    let uu____26608
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26608]
                                                                     in
                                                                    [uu____26605]
                                                                     in
                                                                    let uu____26613
                                                                    =
                                                                    let uu____26614
                                                                    =
                                                                    let uu____26619
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26619,
                                                                    uu____26620)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26614
                                                                     in
                                                                    (uu____26600,
                                                                    [x],
                                                                    uu____26613)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26589
                                                                     in
                                                                    let uu____26639
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26588,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26639)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26581
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26646
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____26674
                                                                    =
                                                                    let uu____26675
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26675
                                                                    dapp1  in
                                                                    [uu____26674])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26646
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26682
                                                                    =
                                                                    let uu____26689
                                                                    =
                                                                    let uu____26690
                                                                    =
                                                                    let uu____26701
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26712
                                                                    =
                                                                    let uu____26713
                                                                    =
                                                                    let uu____26718
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26718)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26713
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26701,
                                                                    uu____26712)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26690
                                                                     in
                                                                    (uu____26689,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26682)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____26737 ->
                                                        ((let uu____26739 =
                                                            let uu____26744 =
                                                              let uu____26745
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____26746
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____26745
                                                                uu____26746
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____26744)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26739);
                                                         ([], [])))
                                                in
                                             let uu____26751 = encode_elim ()
                                                in
                                             (match uu____26751 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26771 =
                                                      let uu____26774 =
                                                        let uu____26777 =
                                                          let uu____26780 =
                                                            let uu____26783 =
                                                              let uu____26784
                                                                =
                                                                let uu____26795
                                                                  =
                                                                  let uu____26798
                                                                    =
                                                                    let uu____26799
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26799
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26798
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26795)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26784
                                                               in
                                                            [uu____26783]  in
                                                          let uu____26804 =
                                                            let uu____26807 =
                                                              let uu____26810
                                                                =
                                                                let uu____26813
                                                                  =
                                                                  let uu____26816
                                                                    =
                                                                    let uu____26819
                                                                    =
                                                                    let uu____26822
                                                                    =
                                                                    let uu____26823
                                                                    =
                                                                    let uu____26830
                                                                    =
                                                                    let uu____26831
                                                                    =
                                                                    let uu____26842
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26842)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26831
                                                                     in
                                                                    (uu____26830,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26823
                                                                     in
                                                                    let uu____26855
                                                                    =
                                                                    let uu____26858
                                                                    =
                                                                    let uu____26859
                                                                    =
                                                                    let uu____26866
                                                                    =
                                                                    let uu____26867
                                                                    =
                                                                    let uu____26878
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____26889
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26878,
                                                                    uu____26889)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26867
                                                                     in
                                                                    (uu____26866,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26859
                                                                     in
                                                                    [uu____26858]
                                                                     in
                                                                    uu____26822
                                                                    ::
                                                                    uu____26855
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26819
                                                                     in
                                                                  FStar_List.append
                                                                    uu____26816
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26813
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26810
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26807
                                                             in
                                                          FStar_List.append
                                                            uu____26780
                                                            uu____26804
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____26777
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____26774
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26771
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____26935  ->
              fun se  ->
                match uu____26935 with
                | (g,env1) ->
                    let uu____26955 = encode_sigelt env1 se  in
                    (match uu____26955 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____27020 =
        match uu____27020 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____27052 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____27058 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____27058
                   then
                     let uu____27059 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____27060 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____27061 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____27059 uu____27060 uu____27061
                   else ());
                  (let uu____27063 = encode_term t1 env1  in
                   match uu____27063 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____27079 =
                         let uu____27086 =
                           let uu____27087 =
                             let uu____27088 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____27088
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____27087  in
                         new_term_constant_from_string env1 x uu____27086  in
                       (match uu____27079 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____27104 = FStar_Options.log_queries ()
                                 in
                              if uu____27104
                              then
                                let uu____27107 =
                                  let uu____27108 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____27109 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____27110 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____27108 uu____27109 uu____27110
                                   in
                                FStar_Pervasives_Native.Some uu____27107
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____27126,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____27140 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____27140 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____27163,se,uu____27165) ->
                 let uu____27170 = encode_sigelt env1 se  in
                 (match uu____27170 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____27187,se) ->
                 let uu____27193 = encode_sigelt env1 se  in
                 (match uu____27193 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____27210 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____27210 with | (uu____27233,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____27248 'Auu____27249 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____27248,'Auu____27249)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____27318  ->
              match uu____27318 with
              | (l,uu____27330,uu____27331) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____27377  ->
              match uu____27377 with
              | (l,uu____27391,uu____27392) ->
                  let uu____27401 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____27402 =
                    let uu____27405 =
                      let uu____27406 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____27406  in
                    [uu____27405]  in
                  uu____27401 :: uu____27402))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____27433 =
      let uu____27436 =
        let uu____27437 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____27440 =
          let uu____27441 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____27441 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____27437;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____27440
        }  in
      [uu____27436]  in
    FStar_ST.op_Colon_Equals last_env uu____27433
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____27479 = FStar_ST.op_Bang last_env  in
      match uu____27479 with
      | [] -> failwith "No env; call init first!"
      | e::uu____27510 ->
          let uu___133_27513 = e  in
          let uu____27514 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___133_27513.bindings);
            depth = (uu___133_27513.depth);
            tcenv;
            warn = (uu___133_27513.warn);
            cache = (uu___133_27513.cache);
            nolabels = (uu___133_27513.nolabels);
            use_zfuel_name = (uu___133_27513.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_27513.encode_non_total_function_typ);
            current_module_name = uu____27514
          }
  
let (set_env : env_t -> unit) =
  fun env  ->
    let uu____27520 = FStar_ST.op_Bang last_env  in
    match uu____27520 with
    | [] -> failwith "Empty env stack"
    | uu____27550::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____27585  ->
    let uu____27586 = FStar_ST.op_Bang last_env  in
    match uu____27586 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___134_27624 = hd1  in
          {
            bindings = (uu___134_27624.bindings);
            depth = (uu___134_27624.depth);
            tcenv = (uu___134_27624.tcenv);
            warn = (uu___134_27624.warn);
            cache = refs;
            nolabels = (uu___134_27624.nolabels);
            use_zfuel_name = (uu___134_27624.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_27624.encode_non_total_function_typ);
            current_module_name = (uu___134_27624.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____27656  ->
    let uu____27657 = FStar_ST.op_Bang last_env  in
    match uu____27657 with
    | [] -> failwith "Popping an empty stack"
    | uu____27687::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> unit) =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let (pop : Prims.string -> unit) =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let (open_fact_db_tags :
  env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list) = fun env  -> [] 
let (place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____27769::uu____27770,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___135_27778 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___135_27778.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___135_27778.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___135_27778.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27779 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____27798 =
        let uu____27801 =
          let uu____27802 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27802  in
        let uu____27803 = open_fact_db_tags env  in uu____27801 ::
          uu____27803
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27798
  
let (encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____27829 = encode_sigelt env se  in
      match uu____27829 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____27871 = FStar_Options.log_queries ()  in
        if uu____27871
        then
          let uu____27874 =
            let uu____27875 =
              let uu____27876 =
                let uu____27877 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27877 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27876  in
            FStar_SMTEncoding_Term.Caption uu____27875  in
          uu____27874 :: decls
        else decls  in
      (let uu____27888 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27888
       then
         let uu____27889 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27889
       else ());
      (let env =
         let uu____27892 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____27892 tcenv  in
       let uu____27893 = encode_top_level_facts env se  in
       match uu____27893 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27907 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____27907)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____27923 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27923
       then
         let uu____27924 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27924
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27963  ->
                 fun se  ->
                   match uu____27963 with
                   | (g,env2) ->
                       let uu____27983 = encode_top_level_facts env2 se  in
                       (match uu____27983 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____28006 =
         encode_signature
           (let uu___136_28015 = env  in
            {
              bindings = (uu___136_28015.bindings);
              depth = (uu___136_28015.depth);
              tcenv = (uu___136_28015.tcenv);
              warn = false;
              cache = (uu___136_28015.cache);
              nolabels = (uu___136_28015.nolabels);
              use_zfuel_name = (uu___136_28015.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___136_28015.encode_non_total_function_typ);
              current_module_name = (uu___136_28015.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____28006 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____28034 = FStar_Options.log_queries ()  in
             if uu____28034
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___137_28042 = env1  in
               {
                 bindings = (uu___137_28042.bindings);
                 depth = (uu___137_28042.depth);
                 tcenv = (uu___137_28042.tcenv);
                 warn = true;
                 cache = (uu___137_28042.cache);
                 nolabels = (uu___137_28042.nolabels);
                 use_zfuel_name = (uu___137_28042.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___137_28042.encode_non_total_function_typ);
                 current_module_name = (uu___137_28042.current_module_name)
               });
            (let uu____28044 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____28044
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____28102 =
           let uu____28103 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____28103.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____28102);
        (let env =
           let uu____28105 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____28105 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____28117 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____28154 = aux rest  in
                 (match uu____28154 with
                  | (out,rest1) ->
                      let t =
                        let uu____28184 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____28184 with
                        | FStar_Pervasives_Native.Some uu____28189 ->
                            let uu____28190 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____28190
                              x.FStar_Syntax_Syntax.sort
                        | uu____28191 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____28195 =
                        let uu____28198 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___138_28201 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___138_28201.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___138_28201.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____28198 :: out  in
                      (uu____28195, rest1))
             | uu____28206 -> ([], bindings1)  in
           let uu____28213 = aux bindings  in
           match uu____28213 with
           | (closing,bindings1) ->
               let uu____28238 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____28238, bindings1)
            in
         match uu____28117 with
         | (q1,bindings1) ->
             let uu____28261 =
               let uu____28266 =
                 FStar_List.filter
                   (fun uu___103_28271  ->
                      match uu___103_28271 with
                      | FStar_TypeChecker_Env.Binding_sig uu____28272 ->
                          false
                      | uu____28279 -> true) bindings1
                  in
               encode_env_bindings env uu____28266  in
             (match uu____28261 with
              | (env_decls,env1) ->
                  ((let uu____28297 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____28297
                    then
                      let uu____28298 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____28298
                    else ());
                   (let uu____28300 = encode_formula q1 env1  in
                    match uu____28300 with
                    | (phi,qdecls) ->
                        let uu____28321 =
                          let uu____28326 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____28326 phi
                           in
                        (match uu____28321 with
                         | (labels,phi1) ->
                             let uu____28343 = encode_labels labels  in
                             (match uu____28343 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____28380 =
                                      let uu____28387 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____28388 =
                                        varops.mk_unique "@query"  in
                                      (uu____28387,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____28388)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____28380
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  