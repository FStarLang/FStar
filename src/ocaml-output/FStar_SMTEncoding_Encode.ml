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
      (fun uu___83_124  ->
         match uu___83_124 with
         | (FStar_Util.Inl uu____133,uu____134) -> false
         | uu____139 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___106_166 = a  in
        let uu____167 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____167;
          FStar_Syntax_Syntax.index =
            (uu___106_166.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___106_166.FStar_Syntax_Syntax.sort)
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
  let new_scope uu____794 =
    let uu____795 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____798 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____795, uu____798)  in
  let scopes =
    let uu____818 = let uu____829 = new_scope ()  in [uu____829]  in
    FStar_Util.mk_ref uu____818  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____872 =
        let uu____875 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____875
          (fun uu____962  ->
             match uu____962 with
             | (names1,uu____974) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____872 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____983 ->
          (FStar_Util.incr ctr;
           (let uu____1018 =
              let uu____1019 =
                let uu____1020 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1020  in
              Prims.strcat "__" uu____1019  in
            Prims.strcat y1 uu____1018))
       in
    let top_scope =
      let uu____1069 =
        let uu____1078 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1078
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1069  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1199 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1285 =
      let uu____1286 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1286  in
    FStar_Util.format2 "%s_%s" pfx uu____1285  in
  let string_const s =
    let uu____1293 =
      let uu____1296 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1296
        (fun uu____1383  ->
           match uu____1383 with
           | (uu____1394,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1293 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1407 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1407  in
        let top_scope =
          let uu____1411 =
            let uu____1420 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1420  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1411  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1524 =
    let uu____1525 =
      let uu____1536 = new_scope ()  in
      let uu____1545 = FStar_ST.op_Bang scopes  in uu____1536 :: uu____1545
       in
    FStar_ST.op_Colon_Equals scopes uu____1525  in
  let pop1 uu____1699 =
    let uu____1700 =
      let uu____1711 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1711
       in
    FStar_ST.op_Colon_Equals scopes uu____1700  in
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
    let uu___107_1865 = x  in
    let uu____1866 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1866;
      FStar_Syntax_Syntax.index = (uu___107_1865.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___107_1865.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1998 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____2024 -> false
  
let (__proj__Binding_fvar__item___0 : binding -> fvar_binding) =
  fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____2038 'Auu____2039 .
    'Auu____2038 ->
      ('Auu____2038,'Auu____2039 FStar_Pervasives_Native.option)
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
  'Auu____2380 .
    'Auu____2380 ->
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
                 (fun uu___84_2418  ->
                    match uu___84_2418 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2422 -> []))
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
    let vars =
      let uu____2438 =
        FStar_Util.prefix_until
          (fun uu___85_2453  ->
             match uu___85_2453 with
             | Binding_fvar uu____2454 -> true
             | uu____2455 -> false) e.bindings
         in
      match uu____2438 with
      | FStar_Pervasives_Native.None  -> e.bindings
      | FStar_Pervasives_Native.Some (vars,fv,uu____2470) ->
          FStar_List.append vars [fv]
       in
    let uu____2489 =
      FStar_All.pipe_right vars
        (FStar_List.map
           (fun uu___86_2499  ->
              match uu___86_2499 with
              | Binding_var (x,uu____2501) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid))
       in
    FStar_All.pipe_right uu____2489 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2511 .
    env_t ->
      (binding -> 'Auu____2511 FStar_Pervasives_Native.option) ->
        'Auu____2511 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2545 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2545
      then
        let uu____2548 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2548
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
      let uu____2565 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2565)
  
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
        (let uu___108_2585 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___108_2585.tcenv);
           warn = (uu___108_2585.warn);
           cache = (uu___108_2585.cache);
           nolabels = (uu___108_2585.nolabels);
           use_zfuel_name = (uu___108_2585.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___108_2585.encode_non_total_function_typ);
           current_module_name = (uu___108_2585.current_module_name)
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
        (let uu___109_2607 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___109_2607.depth);
           tcenv = (uu___109_2607.tcenv);
           warn = (uu___109_2607.warn);
           cache = (uu___109_2607.cache);
           nolabels = (uu___109_2607.nolabels);
           use_zfuel_name = (uu___109_2607.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___109_2607.encode_non_total_function_typ);
           current_module_name = (uu___109_2607.current_module_name)
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
          (let uu___110_2634 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___110_2634.depth);
             tcenv = (uu___110_2634.tcenv);
             warn = (uu___110_2634.warn);
             cache = (uu___110_2634.cache);
             nolabels = (uu___110_2634.nolabels);
             use_zfuel_name = (uu___110_2634.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___110_2634.encode_non_total_function_typ);
             current_module_name = (uu___110_2634.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___111_2650 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___111_2650.depth);
          tcenv = (uu___111_2650.tcenv);
          warn = (uu___111_2650.warn);
          cache = (uu___111_2650.cache);
          nolabels = (uu___111_2650.nolabels);
          use_zfuel_name = (uu___111_2650.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___111_2650.encode_non_total_function_typ);
          current_module_name = (uu___111_2650.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___87_2680  ->
             match uu___87_2680 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2693 -> FStar_Pervasives_Native.None)
         in
      let uu____2698 = aux a  in
      match uu____2698 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2710 = aux a2  in
          (match uu____2710 with
           | FStar_Pervasives_Native.None  ->
               let uu____2721 =
                 let uu____2722 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2723 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2722 uu____2723
                  in
               failwith uu____2721
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
  
let (aux_check_push_fvar : env_t -> fvar_binding -> env_t) =
  fun env  ->
    fun fvb  ->
      let uu___112_2779 = env  in
      {
        bindings = ((Binding_fvar fvb) :: (env.bindings));
        depth = (uu___112_2779.depth);
        tcenv = (uu___112_2779.tcenv);
        warn = (uu___112_2779.warn);
        cache = (uu___112_2779.cache);
        nolabels = (uu___112_2779.nolabels);
        use_zfuel_name = (uu___112_2779.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___112_2779.encode_non_total_function_typ);
        current_module_name = (uu___112_2779.current_module_name)
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
        (fname, ftok_name, (aux_check_push_fvar env fvb))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___88_2821  ->
           match uu___88_2821 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2825 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2836 =
        lookup_binding env
          (fun uu___89_2841  ->
             match uu___89_2841 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2845 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2836 FStar_Option.isSome
  
let (lookup_lid : env_t -> FStar_Ident.lid -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2858 = try_lookup_lid env a  in
      match uu____2858 with
      | FStar_Pervasives_Native.None  ->
          let uu____2861 =
            let uu____2862 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2862  in
          failwith uu____2861
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
            aux_check_push_fvar env fvb
  
let (replace_free_var :
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
            let env1 =
              match env.bindings with
              | (Binding_fvar fvb1)::bs when
                  FStar_Ident.lid_equals fvb1.fvar_lid x ->
                  let uu___113_2929 = env  in
                  {
                    bindings = bs;
                    depth = (uu___113_2929.depth);
                    tcenv = (uu___113_2929.tcenv);
                    warn = (uu___113_2929.warn);
                    cache = (uu___113_2929.cache);
                    nolabels = (uu___113_2929.nolabels);
                    use_zfuel_name = (uu___113_2929.use_zfuel_name);
                    encode_non_total_function_typ =
                      (uu___113_2929.encode_non_total_function_typ);
                    current_module_name = (uu___113_2929.current_module_name)
                  }
              | uu____2930 ->
                  failwith "replace_free_var: unexpected binding at the head"
               in
            aux_check_push_fvar env1 fvb
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2950 =
            let uu____2957 =
              let uu____2960 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2960]  in
            (f, uu____2957)  in
          FStar_SMTEncoding_Util.mkApp uu____2950  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        aux_check_push_fvar env fvb1
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2978 = try_lookup_lid env l  in
      match uu____2978 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2987 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2995,fuel::[]) ->
                         let uu____2999 =
                           let uu____3000 =
                             let uu____3001 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____3001
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____3000 "fuel"  in
                         if uu____2999
                         then
                           let uu____3012 =
                             let uu____3013 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3013
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_17  ->
                                FStar_Pervasives_Native.Some _0_17)
                             uu____3012
                         else FStar_Pervasives_Native.Some t
                     | uu____3017 -> FStar_Pervasives_Native.Some t)
                | uu____3018 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____3035 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3035 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3039 =
            let uu____3040 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3040  in
          failwith uu____3039
  
let (lookup_free_var_name :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      ((fvb.smt_id), (fvb.smt_arity))
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list,
        Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____3093;
            FStar_SMTEncoding_Term.rng = uu____3094;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____3109 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____3137 ->
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
        (fun uu___90_3154  ->
           match uu___90_3154 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____3158 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3165 .
    'Auu____3165 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3185  ->
      match uu____3185 with
      | (pats,vars,body) ->
          let fallback uu____3212 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3217 = FStar_Options.unthrottle_inductives ()  in
          if uu____3217
          then fallback ()
          else
            (let uu____3219 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3219 with
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
                           | uu____3252 -> p))
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
                             let uu____3273 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3273
                         | uu____3276 ->
                             let uu____3277 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3277 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3282 -> body  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3323 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3336 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3343 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3344 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3345 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3362 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3364 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3364 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3382;
             FStar_Syntax_Syntax.vars = uu____3383;_},uu____3384)
          ->
          let uu____3405 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3405 FStar_Option.isNone
      | uu____3422 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____3433 =
        let uu____3434 = FStar_Syntax_Util.un_uinst t  in
        uu____3434.FStar_Syntax_Syntax.n  in
      match uu____3433 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3437,uu____3438,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___91_3459  ->
                  match uu___91_3459 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3460 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3462 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3462 FStar_Option.isSome
      | uu____3479 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____3490 = head_normal env t  in
      if uu____3490
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
    let uu____3507 =
      let uu____3508 = FStar_Syntax_Syntax.null_binder t  in [uu____3508]  in
    let uu____3521 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3507 uu____3521 FStar_Pervasives_Native.None
  
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
                    let uu____3565 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3565
                | s ->
                    let uu____3568 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3568) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'Auu____3595 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3595
  =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____3616 =
            let uu____3621 =
              let uu____3622 = FStar_Util.string_of_int arity  in
              let uu____3623 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3622 uu____3623
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3621)  in
          FStar_Errors.raise_error uu____3616 rng
  
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
              (let uu____3662 = FStar_Util.first_N arity args  in
               match uu____3662 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3685 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3685 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___92_3694  ->
    match uu___92_3694 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3695 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____3741;
                       FStar_SMTEncoding_Term.rng = uu____3742;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3765) ->
              let uu____3774 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3785 -> false) args (FStar_List.rev xs))
                 in
              if uu____3774
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3789,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3793 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3799 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3799))
                 in
              if uu____3793
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3803 -> FStar_Pervasives_Native.None  in
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
    | uu____4063 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____4069 -> false
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4096 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4109 ->
            let uu____4116 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____4116
        | uu____4117 ->
            if norm1
            then let uu____4118 = whnf env t1  in aux false uu____4118
            else
              (let uu____4120 =
                 let uu____4121 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____4122 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4121 uu____4122
                  in
               failwith uu____4120)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4168) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4173 ->
        let uu____4174 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4174)
  
let is_arithmetic_primitive :
  'Auu____4191 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4191 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4213::uu____4214::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4218::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4221 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4244 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4261 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4268 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4268)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4309)::uu____4310::uu____4311::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4362)::uu____4363::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4400 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4703 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4703, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4704 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4704, [])
      | FStar_Const.Const_char c1 ->
          let uu____4706 =
            let uu____4707 =
              let uu____4714 =
                let uu____4717 =
                  let uu____4718 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4718  in
                [uu____4717]  in
              ("FStar.Char.__char_of_int", uu____4714)  in
            FStar_SMTEncoding_Util.mkApp uu____4707  in
          (uu____4706, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4734 =
            let uu____4735 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4735  in
          (uu____4734, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4756) ->
          let uu____4757 = varops.string_const s  in (uu____4757, [])
      | FStar_Const.Const_range uu____4760 ->
          let uu____4761 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4761, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4765 =
            let uu____4766 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4766  in
          failwith uu____4765

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
        (let uu____4793 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4793
         then
           let uu____4794 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4794
         else ());
        (let uu____4796 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4886  ->
                   fun b  ->
                     match uu____4886 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4965 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4981 = gen_term_var env1 x  in
                           match uu____4981 with
                           | (xxsym,xx,env') ->
                               let uu____5005 =
                                 let uu____5010 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____5010 env1 xx
                                  in
                               (match uu____5005 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4965 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4796 with
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
          let uu____5163 = encode_term t env  in
          match uu____5163 with
          | (t1,decls) ->
              let uu____5174 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5174, decls)

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
          let uu____5185 = encode_term t env  in
          match uu____5185 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5200 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5200, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5202 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5202, decls))

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
        let uu____5208 = encode_args args_e env  in
        match uu____5208 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5227 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5238 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5238  in
            let binary arg_tms1 =
              let uu____5253 =
                let uu____5254 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5254  in
              let uu____5255 =
                let uu____5256 =
                  let uu____5257 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5257  in
                FStar_SMTEncoding_Term.unboxInt uu____5256  in
              (uu____5253, uu____5255)  in
            let mk_default uu____5265 =
              let uu____5266 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5266 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____5328 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5328
              then
                let uu____5329 =
                  let uu____5330 = mk_args ts  in op uu____5330  in
                FStar_All.pipe_right uu____5329 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5365 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5365
              then
                let uu____5366 = binary ts  in
                match uu____5366 with
                | (t1,t2) ->
                    let uu____5373 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5373
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5377 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5377
                 then
                   let uu____5378 =
                     let uu____5379 = binary ts  in op uu____5379  in
                   FStar_All.pipe_right uu____5378
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
            let uu____5540 =
              let uu____5550 =
                FStar_List.tryFind
                  (fun uu____5574  ->
                     match uu____5574 with
                     | (l,uu____5584) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5550 FStar_Util.must  in
            (match uu____5540 with
             | (uu____5628,op) ->
                 let uu____5640 = op arg_tms  in (uu____5640, decls))

and (encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5654 = FStar_List.hd args_e  in
        match uu____5654 with
        | (tm_sz,uu____5662) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5672 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5672 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____5680 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5680);
                   t_decls1)
               in
            let uu____5681 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5703::(sz_arg,uu____5705)::uu____5706::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5755 =
                    let uu____5764 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5764  in
                  let uu____5785 =
                    let uu____5788 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5788  in
                  (uu____5755, uu____5785)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5800::(sz_arg,uu____5802)::uu____5803::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5852 =
                    let uu____5853 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5853
                     in
                  failwith uu____5852
              | uu____5860 ->
                  let uu____5873 = FStar_List.tail args_e  in
                  (uu____5873, FStar_Pervasives_Native.None)
               in
            (match uu____5681 with
             | (arg_tms,ext_sz) ->
                 let uu____5910 = encode_args arg_tms env  in
                 (match uu____5910 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5931 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5942 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5942  in
                      let unary_arith arg_tms2 =
                        let uu____5953 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5953  in
                      let binary arg_tms2 =
                        let uu____5968 =
                          let uu____5969 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5969
                           in
                        let uu____5970 =
                          let uu____5971 =
                            let uu____5972 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5972  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5971
                           in
                        (uu____5968, uu____5970)  in
                      let binary_arith arg_tms2 =
                        let uu____5989 =
                          let uu____5990 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5990
                           in
                        let uu____5991 =
                          let uu____5992 =
                            let uu____5993 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5993  in
                          FStar_SMTEncoding_Term.unboxInt uu____5992  in
                        (uu____5989, uu____5991)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____6051 =
                          let uu____6052 = mk_args ts  in op uu____6052  in
                        FStar_All.pipe_right uu____6051 resBox  in
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
                        let uu____6184 =
                          let uu____6189 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____6189  in
                        let uu____6191 =
                          let uu____6196 =
                            let uu____6197 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____6197  in
                          FStar_SMTEncoding_Term.boxBitVec uu____6196  in
                        mk_bv uu____6184 unary uu____6191 arg_tms2  in
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
                      let uu____6430 =
                        let uu____6440 =
                          FStar_List.tryFind
                            (fun uu____6464  ->
                               match uu____6464 with
                               | (l,uu____6474) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6440 FStar_Util.must  in
                      (match uu____6430 with
                       | (uu____6520,op) ->
                           let uu____6532 = op arg_tms1  in
                           (uu____6532, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6543 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6543
       then
         let uu____6544 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6545 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6546 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6544 uu____6545
           uu____6546
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6552 ->
           let uu____6577 =
             let uu____6578 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6579 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6580 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6581 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6578
               uu____6579 uu____6580 uu____6581
              in
           failwith uu____6577
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6586 =
             let uu____6587 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6588 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6589 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6590 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6587
               uu____6588 uu____6589 uu____6590
              in
           failwith uu____6586
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6596 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____6596 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6598 =
             let uu____6599 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6599
              in
           failwith uu____6598
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____6606),uu____6607) ->
           let uu____6656 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____6664 -> false  in
           if uu____6656
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____6679) ->
           let tv =
             let uu____6685 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____6685
              in
           let t1 =
             let uu____6689 =
               let uu____6698 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____6698]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____6689
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6718) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6726 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6726, [])
       | FStar_Syntax_Syntax.Tm_type uu____6727 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6729) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6754 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6754 with
            | (binders1,res) ->
                let uu____6765 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6765
                then
                  let uu____6770 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6770 with
                   | (vars,guards,env',decls,uu____6795) ->
                       let fsym =
                         let uu____6813 = varops.fresh "f"  in
                         (uu____6813, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6816 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___114_6825 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___114_6825.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___114_6825.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___114_6825.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___114_6825.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___114_6825.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___114_6825.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___114_6825.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___114_6825.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___114_6825.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___114_6825.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___114_6825.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___114_6825.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___114_6825.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___114_6825.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___114_6825.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___114_6825.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___114_6825.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___114_6825.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___114_6825.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___114_6825.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___114_6825.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___114_6825.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___114_6825.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___114_6825.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___114_6825.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___114_6825.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___114_6825.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___114_6825.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___114_6825.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___114_6825.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___114_6825.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___114_6825.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___114_6825.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___114_6825.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___114_6825.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___114_6825.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___114_6825.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6816 with
                        | (pre_opt,res_t) ->
                            let uu____6836 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6836 with
                             | (res_pred,decls') ->
                                 let uu____6847 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6860 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6860, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6864 =
                                         encode_formula pre env'  in
                                       (match uu____6864 with
                                        | (guard,decls0) ->
                                            let uu____6877 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6877, decls0))
                                    in
                                 (match uu____6847 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6889 =
                                          let uu____6900 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6900)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6889
                                         in
                                      let cvars =
                                        let uu____6916 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6916
                                          (FStar_List.filter
                                             (fun uu____6942  ->
                                                match uu____6942 with
                                                | (x,uu____6948) ->
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
                                      let uu____6961 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6961 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6969 =
                                             let uu____6970 =
                                               let uu____6977 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6977)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6970
                                              in
                                           (uu____6969,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6995 =
                                               let uu____6996 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6996
                                                in
                                             varops.mk_unique uu____6995  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____7005 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____7005
                                             then
                                               let uu____7006 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7006
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
                                             let uu____7012 =
                                               let uu____7019 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____7019)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7012
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
                                             let uu____7031 =
                                               let uu____7038 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____7038,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7031
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
                                             let uu____7051 =
                                               let uu____7058 =
                                                 let uu____7059 =
                                                   let uu____7070 =
                                                     let uu____7071 =
                                                       let uu____7076 =
                                                         let uu____7077 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____7077
                                                          in
                                                       (f_has_t, uu____7076)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____7071
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____7070)
                                                    in
                                                 mkForall_fuel uu____7059  in
                                               (uu____7058,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7051
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____7092 =
                                               let uu____7099 =
                                                 let uu____7100 =
                                                   let uu____7111 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____7111)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____7100
                                                  in
                                               (uu____7099,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7092
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
                                           ((let uu____7128 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____7128);
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
                     let uu____7139 =
                       let uu____7146 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____7146,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7139  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____7156 =
                       let uu____7163 =
                         let uu____7164 =
                           let uu____7175 =
                             let uu____7176 =
                               let uu____7181 =
                                 let uu____7182 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____7182
                                  in
                               (f_has_t, uu____7181)  in
                             FStar_SMTEncoding_Util.mkImp uu____7176  in
                           ([[f_has_t]], [fsym], uu____7175)  in
                         mkForall_fuel uu____7164  in
                       (uu____7163, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7156  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____7199 ->
           let uu____7206 =
             let uu____7211 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____7211 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____7218;
                 FStar_Syntax_Syntax.vars = uu____7219;_} ->
                 let uu____7226 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____7226 with
                  | (b,f1) ->
                      let uu____7247 =
                        let uu____7248 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7248  in
                      (uu____7247, f1))
             | uu____7257 -> failwith "impossible"  in
           (match uu____7206 with
            | (x,f) ->
                let uu____7268 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7268 with
                 | (base_t,decls) ->
                     let uu____7279 = gen_term_var env x  in
                     (match uu____7279 with
                      | (x1,xtm,env') ->
                          let uu____7293 = encode_formula f env'  in
                          (match uu____7293 with
                           | (refinement,decls') ->
                               let uu____7304 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7304 with
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
                                      let uu____7324 =
                                        let uu____7331 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7338 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7331
                                          uu____7338
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7324
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7379  ->
                                              match uu____7379 with
                                              | (y,uu____7385) ->
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
                                    let uu____7412 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7412 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7420 =
                                           let uu____7421 =
                                             let uu____7428 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7428)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7421
                                            in
                                         (uu____7420,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7447 =
                                             let uu____7448 =
                                               let uu____7449 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7449
                                                in
                                             Prims.strcat module_name
                                               uu____7448
                                              in
                                           varops.mk_unique uu____7447  in
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
                                           let uu____7461 =
                                             let uu____7468 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7468)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7461
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
                                           let uu____7483 =
                                             let uu____7490 =
                                               let uu____7491 =
                                                 let uu____7502 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7502)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7491
                                                in
                                             (uu____7490,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7483
                                            in
                                         let t_kinding =
                                           let uu____7512 =
                                             let uu____7519 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7519,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7512
                                            in
                                         let t_interp =
                                           let uu____7529 =
                                             let uu____7536 =
                                               let uu____7537 =
                                                 let uu____7548 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7548)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7537
                                                in
                                             let uu____7565 =
                                               let uu____7566 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7566
                                                in
                                             (uu____7536, uu____7565,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7529
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7571 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7571);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar uv ->
           let ttm =
             let uu____7574 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7574  in
           let uu____7575 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____7575 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7587 =
                    let uu____7594 =
                      let uu____7595 =
                        let uu____7596 =
                          let uu____7597 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7597
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7596  in
                      varops.mk_unique uu____7595  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7594)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7587  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7598 ->
           let uu____7613 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7613 with
            | (head1,args_e) ->
                let uu____7654 =
                  let uu____7665 =
                    let uu____7666 = FStar_Syntax_Subst.compress head1  in
                    uu____7666.FStar_Syntax_Syntax.n  in
                  (uu____7665, args_e)  in
                (match uu____7654 with
                 | uu____7679 when head_redex env head1 ->
                     let uu____7690 = whnf env t  in
                     encode_term uu____7690 env
                 | uu____7691 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7708 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7720;
                       FStar_Syntax_Syntax.vars = uu____7721;_},uu____7722),uu____7723::
                    (v1,uu____7725)::(v2,uu____7727)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7758 = encode_term v1 env  in
                     (match uu____7758 with
                      | (v11,decls1) ->
                          let uu____7769 = encode_term v2 env  in
                          (match uu____7769 with
                           | (v21,decls2) ->
                               let uu____7780 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7780,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7782::(v1,uu____7784)::(v2,uu____7786)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7813 = encode_term v1 env  in
                     (match uu____7813 with
                      | (v11,decls1) ->
                          let uu____7824 = encode_term v2 env  in
                          (match uu____7824 with
                           | (v21,decls2) ->
                               let uu____7835 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7835,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7837)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7853)::(rng,uu____7855)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7874) ->
                     let e0 =
                       let uu____7888 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7888
                        in
                     ((let uu____7896 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7896
                       then
                         let uu____7897 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7897
                       else ());
                      (let e =
                         let uu____7902 =
                           let uu____7907 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7908 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7907
                             uu____7908
                            in
                         uu____7902 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7917),(arg,uu____7919)::[]) -> encode_term arg env
                 | uu____7934 ->
                     let uu____7945 = encode_args args_e env  in
                     (match uu____7945 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7998 = encode_term head1 env  in
                            match uu____7998 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____8054 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____8054 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8132  ->
                                                 fun uu____8133  ->
                                                   match (uu____8132,
                                                           uu____8133)
                                                   with
                                                   | ((bv,uu____8155),
                                                      (a,uu____8157)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8175 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8175
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8176 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8176 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8191 =
                                                   let uu____8198 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8207 =
                                                     let uu____8208 =
                                                       let uu____8209 =
                                                         let uu____8210 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8210
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8209
                                                        in
                                                     varops.mk_unique
                                                       uu____8208
                                                      in
                                                   (uu____8198,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8207)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8191
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8227 = lookup_free_var_sym env fv  in
                            match uu____8227 with
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
                                   FStar_Syntax_Syntax.pos = uu____8255;
                                   FStar_Syntax_Syntax.vars = uu____8256;_},uu____8257)
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
                                   FStar_Syntax_Syntax.pos = uu____8268;
                                   FStar_Syntax_Syntax.vars = uu____8269;_},uu____8270)
                                ->
                                let uu____8275 =
                                  let uu____8276 =
                                    let uu____8281 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8281
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8276
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8275
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8311 =
                                  let uu____8312 =
                                    let uu____8317 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8317
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8312
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8311
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8346,(FStar_Util.Inl t1,uu____8348),uu____8349)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8398,(FStar_Util.Inr c,uu____8400),uu____8401)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8450 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8467 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8467
                                  in
                               let uu____8468 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8468 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8502;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8503;_},uu____8504)
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
                                     | uu____8518 ->
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
           let uu____8577 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8577 with
            | (bs1,body1,opening) ->
                let fallback uu____8602 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8607 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8607, [decl])  in
                let is_impure rc =
                  let uu____8616 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8616 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8628 =
                          let uu____8641 =
                            FStar_TypeChecker_Env.get_range env.tcenv  in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8641 env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8628 with
                         | (t1,uu____8643,uu____8644) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8662 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8662
                  then
                    let uu____8665 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8665
                  else
                    (let uu____8667 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8667
                     then
                       let uu____8670 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8670
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8677 =
                         let uu____8682 =
                           let uu____8683 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8683
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8682)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8677);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8685 =
                       (is_impure rc) &&
                         (let uu____8687 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8687)
                        in
                     if uu____8685
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8694 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8694 with
                        | (vars,guards,envbody,decls,uu____8719) ->
                            let body2 =
                              let uu____8733 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8733
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8735 = encode_term body2 envbody  in
                            (match uu____8735 with
                             | (body3,decls') ->
                                 let uu____8746 =
                                   let uu____8755 = codomain_eff rc  in
                                   match uu____8755 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8774 = encode_term tfun env
                                          in
                                       (match uu____8774 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8746 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8806 =
                                          let uu____8817 =
                                            let uu____8818 =
                                              let uu____8823 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8823, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8818
                                             in
                                          ([], vars, uu____8817)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8806
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
                                            let uu____8833 =
                                              let uu____8840 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8840
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8833
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8863 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8863 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8871 =
                                             let uu____8872 =
                                               let uu____8879 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8879)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8872
                                              in
                                           (uu____8871,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8888 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8888 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8897 =
                                                    let uu____8898 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8898 = cache_size
                                                     in
                                                  if uu____8897
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
                                                    let uu____8910 =
                                                      let uu____8911 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8911
                                                       in
                                                    varops.mk_unique
                                                      uu____8910
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
                                                  let uu____8916 =
                                                    let uu____8923 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8923)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8916
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
                                                      let uu____8941 =
                                                        let uu____8942 =
                                                          let uu____8949 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8949,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8942
                                                         in
                                                      [uu____8941]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8960 =
                                                    let uu____8967 =
                                                      let uu____8968 =
                                                        let uu____8979 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8979)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8968
                                                       in
                                                    (uu____8967,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8960
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
                                                ((let uu____8992 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8992);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8993,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8994;
                          FStar_Syntax_Syntax.lbunivs = uu____8995;
                          FStar_Syntax_Syntax.lbtyp = uu____8996;
                          FStar_Syntax_Syntax.lbeff = uu____8997;
                          FStar_Syntax_Syntax.lbdef = uu____8998;
                          FStar_Syntax_Syntax.lbattrs = uu____8999;
                          FStar_Syntax_Syntax.lbpos = uu____9000;_}::uu____9001),uu____9002)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____9032;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____9034;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____9036;
                FStar_Syntax_Syntax.lbpos = uu____9037;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____9061 ->
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
              let uu____9131 =
                let uu____9136 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9136 env  in
              match uu____9131 with
              | (ee1,decls1) ->
                  let uu____9161 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9161 with
                   | (xs,e21) ->
                       let uu____9182 = FStar_List.hd xs  in
                       (match uu____9182 with
                        | (x1,uu____9196) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9198 = encode_body e21 env'  in
                            (match uu____9198 with
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
            let uu____9228 =
              let uu____9235 =
                let uu____9236 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9236  in
              gen_term_var env uu____9235  in
            match uu____9228 with
            | (scrsym,scr',env1) ->
                let uu____9244 = encode_term e env1  in
                (match uu____9244 with
                 | (scr,decls) ->
                     let uu____9255 =
                       let encode_branch b uu____9284 =
                         match uu____9284 with
                         | (else_case,decls1) ->
                             let uu____9303 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9303 with
                              | (p,w,br) ->
                                  let uu____9329 = encode_pat env1 p  in
                                  (match uu____9329 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9366  ->
                                                   match uu____9366 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9373 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9395 =
                                               encode_term w1 env2  in
                                             (match uu____9395 with
                                              | (w2,decls2) ->
                                                  let uu____9408 =
                                                    let uu____9409 =
                                                      let uu____9414 =
                                                        let uu____9415 =
                                                          let uu____9420 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9420)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9415
                                                         in
                                                      (guard, uu____9414)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9409
                                                     in
                                                  (uu____9408, decls2))
                                          in
                                       (match uu____9373 with
                                        | (guard1,decls2) ->
                                            let uu____9433 =
                                              encode_br br env2  in
                                            (match uu____9433 with
                                             | (br1,decls3) ->
                                                 let uu____9446 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9446,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9255 with
                      | (match_tm,decls1) ->
                          let uu____9467 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9467, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____9501 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9501
       then
         let uu____9502 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9502
       else ());
      (let uu____9504 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9504 with
       | (vars,pat_term) ->
           let uu____9521 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9566  ->
                     fun v1  ->
                       match uu____9566 with
                       | (env1,vars1) ->
                           let uu____9618 = gen_term_var env1 v1  in
                           (match uu____9618 with
                            | (xx,uu____9640,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9521 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9715 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9716 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9717 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9725 = encode_const c env1  in
                      (match uu____9725 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9733::uu____9734 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9737 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9758 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9758 with
                        | (uu____9765,uu____9766::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9769 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9802  ->
                                  match uu____9802 with
                                  | (arg,uu____9810) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9816 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9816))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9847) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9878 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9901 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9945  ->
                                  match uu____9945 with
                                  | (arg,uu____9959) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9965 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9965))
                         in
                      FStar_All.pipe_right uu____9901 FStar_List.flatten
                   in
                let pat_term1 uu____9995 = encode_term pat_term env1  in
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
      let uu____10005 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10049  ->
                fun uu____10050  ->
                  match (uu____10049, uu____10050) with
                  | ((tms,decls),(t,uu____10086)) ->
                      let uu____10107 = encode_term t env  in
                      (match uu____10107 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10005 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10164 = FStar_Syntax_Util.list_elements e  in
        match uu____10164 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____10187 =
          let uu____10202 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10202 FStar_Syntax_Util.head_and_args
           in
        match uu____10187 with
        | (head1,args) ->
            let uu____10241 =
              let uu____10254 =
                let uu____10255 = FStar_Syntax_Util.un_uinst head1  in
                uu____10255.FStar_Syntax_Syntax.n  in
              (uu____10254, args)  in
            (match uu____10241 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10269,uu____10270)::(e,uu____10272)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10307 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____10347 =
            let uu____10362 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10362 FStar_Syntax_Util.head_and_args
             in
          match uu____10347 with
          | (head1,args) ->
              let uu____10403 =
                let uu____10416 =
                  let uu____10417 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10417.FStar_Syntax_Syntax.n  in
                (uu____10416, args)  in
              (match uu____10403 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10434)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10461 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10483 = smt_pat_or t1  in
            (match uu____10483 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10499 = list_elements1 e  in
                 FStar_All.pipe_right uu____10499
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10517 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10517
                           (FStar_List.map one_pat)))
             | uu____10528 ->
                 let uu____10533 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10533])
        | uu____10554 ->
            let uu____10557 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10557]
         in
      let uu____10578 =
        let uu____10595 =
          let uu____10596 = FStar_Syntax_Subst.compress t  in
          uu____10596.FStar_Syntax_Syntax.n  in
        match uu____10595 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10633 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10633 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10672;
                        FStar_Syntax_Syntax.effect_name = uu____10673;
                        FStar_Syntax_Syntax.result_typ = uu____10674;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10676)::(post,uu____10678)::(pats,uu____10680)::[];
                        FStar_Syntax_Syntax.flags = uu____10681;_}
                      ->
                      let uu____10722 = lemma_pats pats  in
                      (binders1, pre, post, uu____10722)
                  | uu____10739 -> failwith "impos"))
        | uu____10756 -> failwith "Impos"  in
      match uu____10578 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___115_10798 = env  in
            {
              bindings = (uu___115_10798.bindings);
              depth = (uu___115_10798.depth);
              tcenv = (uu___115_10798.tcenv);
              warn = (uu___115_10798.warn);
              cache = (uu___115_10798.cache);
              nolabels = (uu___115_10798.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___115_10798.encode_non_total_function_typ);
              current_module_name = (uu___115_10798.current_module_name)
            }  in
          let uu____10799 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10799 with
           | (vars,guards,env2,decls,uu____10824) ->
               let uu____10837 =
                 let uu____10852 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10906 =
                             let uu____10917 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10917
                               FStar_List.unzip
                              in
                           match uu____10906 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10852 FStar_List.unzip  in
               (match uu____10837 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___116_11069 = env2  in
                      {
                        bindings = (uu___116_11069.bindings);
                        depth = (uu___116_11069.depth);
                        tcenv = (uu___116_11069.tcenv);
                        warn = (uu___116_11069.warn);
                        cache = (uu___116_11069.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___116_11069.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___116_11069.encode_non_total_function_typ);
                        current_module_name =
                          (uu___116_11069.current_module_name)
                      }  in
                    let uu____11070 =
                      let uu____11075 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____11075 env3  in
                    (match uu____11070 with
                     | (pre1,decls'') ->
                         let uu____11082 =
                           let uu____11087 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____11087 env3  in
                         (match uu____11082 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____11097 =
                                let uu____11098 =
                                  let uu____11109 =
                                    let uu____11110 =
                                      let uu____11115 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____11115, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____11110
                                     in
                                  (pats, vars, uu____11109)  in
                                FStar_SMTEncoding_Util.mkForall uu____11098
                                 in
                              (uu____11097, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11124 = FStar_Syntax_Util.head_and_args t  in
      match uu____11124 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11181::(x,uu____11183)::(t1,uu____11185)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11212 = encode_term x env  in
               (match uu____11212 with
                | (x1,decls) ->
                    let uu____11225 = encode_term t1 env  in
                    (match uu____11225 with
                     | (t2,decls') ->
                         let uu____11238 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11238, (FStar_List.append decls decls'))))
           | uu____11241 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11264 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11264
        then
          let uu____11265 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11266 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11265 uu____11266
        else ()  in
      let enc f r l =
        let uu____11305 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11333 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11333 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11305 with
        | (decls,args) ->
            let uu____11362 =
              let uu___117_11363 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11363.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11363.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11362, decls)
         in
      let const_op f r uu____11388 =
        let uu____11391 = f r  in (uu____11391, [])  in
      let un_op f l =
        let uu____11414 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11414  in
      let bin_op f uu___93_11434 =
        match uu___93_11434 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11445 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11485 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11508  ->
                 match uu____11508 with
                 | (t,uu____11522) ->
                     let uu____11523 = encode_formula t env  in
                     (match uu____11523 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11485 with
        | (decls,phis) ->
            let uu____11552 =
              let uu___118_11553 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___118_11553.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___118_11553.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11552, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11616  ->
               match uu____11616 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11635) -> false
                    | uu____11636 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11651 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11651
        else
          (let uu____11665 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11665 r rf)
         in
      let mk_imp1 r uu___94_11700 =
        match uu___94_11700 with
        | (lhs,uu____11706)::(rhs,uu____11708)::[] ->
            let uu____11735 = encode_formula rhs env  in
            (match uu____11735 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11750) ->
                      (l1, decls1)
                  | uu____11755 ->
                      let uu____11756 = encode_formula lhs env  in
                      (match uu____11756 with
                       | (l2,decls2) ->
                           let uu____11767 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11767, (FStar_List.append decls1 decls2)))))
        | uu____11768 -> failwith "impossible"  in
      let mk_ite r uu___95_11795 =
        match uu___95_11795 with
        | (guard,uu____11801)::(_then,uu____11803)::(_else,uu____11805)::[]
            ->
            let uu____11842 = encode_formula guard env  in
            (match uu____11842 with
             | (g,decls1) ->
                 let uu____11853 = encode_formula _then env  in
                 (match uu____11853 with
                  | (t,decls2) ->
                      let uu____11864 = encode_formula _else env  in
                      (match uu____11864 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11876 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11905 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11905  in
      let connectives =
        let uu____11925 =
          let uu____11940 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11940)  in
        let uu____11963 =
          let uu____11980 =
            let uu____11995 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11995)  in
          let uu____12018 =
            let uu____12035 =
              let uu____12052 =
                let uu____12067 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12067)  in
              let uu____12090 =
                let uu____12107 =
                  let uu____12124 =
                    let uu____12139 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12139)  in
                  [uu____12124;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12107  in
              uu____12052 :: uu____12090  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____12035  in
          uu____11980 :: uu____12018  in
        uu____11925 :: uu____11963  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12424 = encode_formula phi' env  in
            (match uu____12424 with
             | (phi2,decls) ->
                 let uu____12435 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12435, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12436 ->
            let uu____12443 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12443 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12482 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12482 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12494;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12496;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12498;
                 FStar_Syntax_Syntax.lbpos = uu____12499;_}::[]),e2)
            ->
            let uu____12523 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12523 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12568::(x,uu____12570)::(t,uu____12572)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12599 = encode_term x env  in
                 (match uu____12599 with
                  | (x1,decls) ->
                      let uu____12610 = encode_term t env  in
                      (match uu____12610 with
                       | (t1,decls') ->
                           let uu____12621 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12621, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12626)::(msg,uu____12628)::(phi2,uu____12630)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12653 =
                   let uu____12658 =
                     let uu____12659 = FStar_Syntax_Subst.compress r  in
                     uu____12659.FStar_Syntax_Syntax.n  in
                   let uu____12662 =
                     let uu____12663 = FStar_Syntax_Subst.compress msg  in
                     uu____12663.FStar_Syntax_Syntax.n  in
                   (uu____12658, uu____12662)  in
                 (match uu____12653 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12672))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12678 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12685)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12700 when head_redex env head2 ->
                 let uu____12711 = whnf env phi1  in
                 encode_formula uu____12711 env
             | uu____12712 ->
                 let uu____12723 = encode_term phi1 env  in
                 (match uu____12723 with
                  | (tt,decls) ->
                      let uu____12734 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___119_12737 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___119_12737.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___119_12737.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12734, decls)))
        | uu____12738 ->
            let uu____12739 = encode_term phi1 env  in
            (match uu____12739 with
             | (tt,decls) ->
                 let uu____12750 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___120_12753 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___120_12753.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___120_12753.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12750, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12797 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12797 with
        | (vars,guards,env2,decls,uu____12836) ->
            let uu____12849 =
              let uu____12862 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12922 =
                          let uu____12933 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12973  ->
                                    match uu____12973 with
                                    | (t,uu____12987) ->
                                        encode_smt_pattern t
                                          (let uu___121_12993 = env2  in
                                           {
                                             bindings =
                                               (uu___121_12993.bindings);
                                             depth = (uu___121_12993.depth);
                                             tcenv = (uu___121_12993.tcenv);
                                             warn = (uu___121_12993.warn);
                                             cache = (uu___121_12993.cache);
                                             nolabels =
                                               (uu___121_12993.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___121_12993.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___121_12993.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12933 FStar_List.unzip
                           in
                        match uu____12922 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12862 FStar_List.unzip  in
            (match uu____12849 with
             | (pats,decls') ->
                 let uu____13102 = encode_formula body env2  in
                 (match uu____13102 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13134;
                             FStar_SMTEncoding_Term.rng = uu____13135;_}::[])::[]
                            when
                            let uu____13150 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13150 = gf -> []
                        | uu____13151 -> guards  in
                      let uu____13156 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13156, body1,
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
                (fun uu____13220  ->
                   match uu____13220 with
                   | (x,uu____13226) ->
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
               let uu____13234 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13246 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____13246) uu____13234 tl1
                in
             let uu____13249 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13276  ->
                       match uu____13276 with
                       | (b,uu____13282) ->
                           let uu____13283 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____13283))
                in
             (match uu____13249 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13289) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____13303 =
                    let uu____13308 =
                      let uu____13309 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13309
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13308)
                     in
                  FStar_Errors.log_issue pos uu____13303)
          in
       let uu____13310 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13310 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13319 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13385  ->
                     match uu____13385 with
                     | (l,uu____13399) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13319 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13438,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13492 = encode_q_body env vars pats body  in
             match uu____13492 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13537 =
                     let uu____13548 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13548)  in
                   FStar_SMTEncoding_Term.mkForall uu____13537
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13571 = encode_q_body env vars pats body  in
             match uu____13571 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13615 =
                   let uu____13616 =
                     let uu____13627 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13627)  in
                   FStar_SMTEncoding_Term.mkExists uu____13616
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13615, decls))))

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
  let uu____13750 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13750 with
  | (asym,a) ->
      let uu____13757 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13757 with
       | (xsym,x) ->
           let uu____13764 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13764 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13806 =
                      let uu____13817 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13817, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13806  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13839 =
                      let uu____13846 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13846)  in
                    FStar_SMTEncoding_Util.mkApp uu____13839  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13859 =
                    let uu____13862 =
                      let uu____13865 =
                        let uu____13868 =
                          let uu____13869 =
                            let uu____13876 =
                              let uu____13877 =
                                let uu____13888 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13888)  in
                              FStar_SMTEncoding_Util.mkForall uu____13877  in
                            (uu____13876, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13869  in
                        let uu____13897 =
                          let uu____13900 =
                            let uu____13901 =
                              let uu____13908 =
                                let uu____13909 =
                                  let uu____13920 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13920)  in
                                FStar_SMTEncoding_Util.mkForall uu____13909
                                 in
                              (uu____13908,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13901  in
                          [uu____13900]  in
                        uu____13868 :: uu____13897  in
                      xtok_decl :: uu____13865  in
                    xname_decl :: uu____13862  in
                  (xtok1, (FStar_List.length vars), uu____13859)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____14010 =
                    let uu____14026 =
                      let uu____14039 =
                        let uu____14040 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____14040
                         in
                      quant axy uu____14039  in
                    (FStar_Parser_Const.op_Eq, uu____14026)  in
                  let uu____14052 =
                    let uu____14070 =
                      let uu____14086 =
                        let uu____14099 =
                          let uu____14100 =
                            let uu____14101 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14101  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14100
                           in
                        quant axy uu____14099  in
                      (FStar_Parser_Const.op_notEq, uu____14086)  in
                    let uu____14113 =
                      let uu____14131 =
                        let uu____14147 =
                          let uu____14160 =
                            let uu____14161 =
                              let uu____14162 =
                                let uu____14167 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14168 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14167, uu____14168)  in
                              FStar_SMTEncoding_Util.mkLT uu____14162  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14161
                             in
                          quant xy uu____14160  in
                        (FStar_Parser_Const.op_LT, uu____14147)  in
                      let uu____14180 =
                        let uu____14198 =
                          let uu____14214 =
                            let uu____14227 =
                              let uu____14228 =
                                let uu____14229 =
                                  let uu____14234 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14235 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14234, uu____14235)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14229  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14228
                               in
                            quant xy uu____14227  in
                          (FStar_Parser_Const.op_LTE, uu____14214)  in
                        let uu____14247 =
                          let uu____14265 =
                            let uu____14281 =
                              let uu____14294 =
                                let uu____14295 =
                                  let uu____14296 =
                                    let uu____14301 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14302 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14301, uu____14302)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14296  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14295
                                 in
                              quant xy uu____14294  in
                            (FStar_Parser_Const.op_GT, uu____14281)  in
                          let uu____14314 =
                            let uu____14332 =
                              let uu____14348 =
                                let uu____14361 =
                                  let uu____14362 =
                                    let uu____14363 =
                                      let uu____14368 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14369 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14368, uu____14369)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14363
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14362
                                   in
                                quant xy uu____14361  in
                              (FStar_Parser_Const.op_GTE, uu____14348)  in
                            let uu____14381 =
                              let uu____14399 =
                                let uu____14415 =
                                  let uu____14428 =
                                    let uu____14429 =
                                      let uu____14430 =
                                        let uu____14435 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14436 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14435, uu____14436)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14430
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14429
                                     in
                                  quant xy uu____14428  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14415)
                                 in
                              let uu____14448 =
                                let uu____14466 =
                                  let uu____14482 =
                                    let uu____14495 =
                                      let uu____14496 =
                                        let uu____14497 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14497
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14496
                                       in
                                    quant qx uu____14495  in
                                  (FStar_Parser_Const.op_Minus, uu____14482)
                                   in
                                let uu____14509 =
                                  let uu____14527 =
                                    let uu____14543 =
                                      let uu____14556 =
                                        let uu____14557 =
                                          let uu____14558 =
                                            let uu____14563 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14564 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14563, uu____14564)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14558
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14557
                                         in
                                      quant xy uu____14556  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14543)
                                     in
                                  let uu____14576 =
                                    let uu____14594 =
                                      let uu____14610 =
                                        let uu____14623 =
                                          let uu____14624 =
                                            let uu____14625 =
                                              let uu____14630 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14631 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14630, uu____14631)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14625
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14624
                                           in
                                        quant xy uu____14623  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14610)
                                       in
                                    let uu____14643 =
                                      let uu____14661 =
                                        let uu____14677 =
                                          let uu____14690 =
                                            let uu____14691 =
                                              let uu____14692 =
                                                let uu____14697 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14698 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14697, uu____14698)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14692
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14691
                                             in
                                          quant xy uu____14690  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14677)
                                         in
                                      let uu____14710 =
                                        let uu____14728 =
                                          let uu____14744 =
                                            let uu____14757 =
                                              let uu____14758 =
                                                let uu____14759 =
                                                  let uu____14764 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14765 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14764, uu____14765)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14759
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14758
                                               in
                                            quant xy uu____14757  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14744)
                                           in
                                        let uu____14777 =
                                          let uu____14795 =
                                            let uu____14811 =
                                              let uu____14824 =
                                                let uu____14825 =
                                                  let uu____14826 =
                                                    let uu____14831 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____14832 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____14831,
                                                      uu____14832)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14826
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14825
                                                 in
                                              quant xy uu____14824  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14811)
                                             in
                                          let uu____14844 =
                                            let uu____14862 =
                                              let uu____14878 =
                                                let uu____14891 =
                                                  let uu____14892 =
                                                    let uu____14893 =
                                                      let uu____14898 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14899 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14898,
                                                        uu____14899)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14893
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14892
                                                   in
                                                quant xy uu____14891  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14878)
                                               in
                                            let uu____14911 =
                                              let uu____14929 =
                                                let uu____14945 =
                                                  let uu____14958 =
                                                    let uu____14959 =
                                                      let uu____14960 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14960
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14959
                                                     in
                                                  quant qx uu____14958  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14945)
                                                 in
                                              [uu____14929]  in
                                            uu____14862 :: uu____14911  in
                                          uu____14795 :: uu____14844  in
                                        uu____14728 :: uu____14777  in
                                      uu____14661 :: uu____14710  in
                                    uu____14594 :: uu____14643  in
                                  uu____14527 :: uu____14576  in
                                uu____14466 :: uu____14509  in
                              uu____14399 :: uu____14448  in
                            uu____14332 :: uu____14381  in
                          uu____14265 :: uu____14314  in
                        uu____14198 :: uu____14247  in
                      uu____14131 :: uu____14180  in
                    uu____14070 :: uu____14113  in
                  uu____14010 :: uu____14052  in
                let mk1 l v1 =
                  let uu____15231 =
                    let uu____15242 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15312  ->
                              match uu____15312 with
                              | (l',uu____15328) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____15242
                      (FStar_Option.map
                         (fun uu____15404  ->
                            match uu____15404 with | (uu____15427,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____15231 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15518  ->
                          match uu____15518 with
                          | (l',uu____15534) -> FStar_Ident.lid_equals l l'))
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
        let uu____15584 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15584 with
        | (xxsym,xx) ->
            let uu____15591 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15591 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15601 =
                   let uu____15608 =
                     let uu____15609 =
                       let uu____15620 =
                         let uu____15621 =
                           let uu____15626 =
                             let uu____15627 =
                               let uu____15632 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15632)  in
                             FStar_SMTEncoding_Util.mkEq uu____15627  in
                           (xx_has_type, uu____15626)  in
                         FStar_SMTEncoding_Util.mkImp uu____15621  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15620)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15609  in
                   let uu____15651 =
                     let uu____15652 =
                       let uu____15653 =
                         let uu____15654 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15654  in
                       Prims.strcat module_name uu____15653  in
                     varops.mk_unique uu____15652  in
                   (uu____15608, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15651)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15601)
  
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
    let uu____15702 =
      let uu____15703 =
        let uu____15710 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15710, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15703  in
    let uu____15711 =
      let uu____15714 =
        let uu____15715 =
          let uu____15722 =
            let uu____15723 =
              let uu____15734 =
                let uu____15735 =
                  let uu____15740 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15740)  in
                FStar_SMTEncoding_Util.mkImp uu____15735  in
              ([[typing_pred]], [xx], uu____15734)  in
            mkForall_fuel uu____15723  in
          (uu____15722, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15715  in
      [uu____15714]  in
    uu____15702 :: uu____15711  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15780 =
      let uu____15781 =
        let uu____15788 =
          let uu____15789 =
            let uu____15800 =
              let uu____15805 =
                let uu____15808 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15808]  in
              [uu____15805]  in
            let uu____15813 =
              let uu____15814 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15814 tt  in
            (uu____15800, [bb], uu____15813)  in
          FStar_SMTEncoding_Util.mkForall uu____15789  in
        (uu____15788, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15781  in
    let uu____15827 =
      let uu____15830 =
        let uu____15831 =
          let uu____15838 =
            let uu____15839 =
              let uu____15850 =
                let uu____15851 =
                  let uu____15856 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____15856)  in
                FStar_SMTEncoding_Util.mkImp uu____15851  in
              ([[typing_pred]], [xx], uu____15850)  in
            mkForall_fuel uu____15839  in
          (uu____15838, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15831  in
      [uu____15830]  in
    uu____15780 :: uu____15827  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15904 =
        let uu____15905 =
          let uu____15912 =
            let uu____15915 =
              let uu____15918 =
                let uu____15921 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15922 =
                  let uu____15925 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15925]  in
                uu____15921 :: uu____15922  in
              tt :: uu____15918  in
            tt :: uu____15915  in
          ("Prims.Precedes", uu____15912)  in
        FStar_SMTEncoding_Util.mkApp uu____15905  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15904  in
    let precedes_y_x =
      let uu____15929 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15929  in
    let uu____15932 =
      let uu____15933 =
        let uu____15940 =
          let uu____15941 =
            let uu____15952 =
              let uu____15957 =
                let uu____15960 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15960]  in
              [uu____15957]  in
            let uu____15965 =
              let uu____15966 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15966 tt  in
            (uu____15952, [bb], uu____15965)  in
          FStar_SMTEncoding_Util.mkForall uu____15941  in
        (uu____15940, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15933  in
    let uu____15979 =
      let uu____15982 =
        let uu____15983 =
          let uu____15990 =
            let uu____15991 =
              let uu____16002 =
                let uu____16003 =
                  let uu____16008 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____16008)  in
                FStar_SMTEncoding_Util.mkImp uu____16003  in
              ([[typing_pred]], [xx], uu____16002)  in
            mkForall_fuel uu____15991  in
          (uu____15990, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15983  in
      let uu____16025 =
        let uu____16028 =
          let uu____16029 =
            let uu____16036 =
              let uu____16037 =
                let uu____16048 =
                  let uu____16049 =
                    let uu____16054 =
                      let uu____16055 =
                        let uu____16058 =
                          let uu____16061 =
                            let uu____16064 =
                              let uu____16065 =
                                let uu____16070 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____16071 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____16070, uu____16071)  in
                              FStar_SMTEncoding_Util.mkGT uu____16065  in
                            let uu____16072 =
                              let uu____16075 =
                                let uu____16076 =
                                  let uu____16081 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____16082 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____16081, uu____16082)  in
                                FStar_SMTEncoding_Util.mkGTE uu____16076  in
                              let uu____16083 =
                                let uu____16086 =
                                  let uu____16087 =
                                    let uu____16092 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____16093 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____16092, uu____16093)  in
                                  FStar_SMTEncoding_Util.mkLT uu____16087  in
                                [uu____16086]  in
                              uu____16075 :: uu____16083  in
                            uu____16064 :: uu____16072  in
                          typing_pred_y :: uu____16061  in
                        typing_pred :: uu____16058  in
                      FStar_SMTEncoding_Util.mk_and_l uu____16055  in
                    (uu____16054, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____16049  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____16048)
                 in
              mkForall_fuel uu____16037  in
            (uu____16036,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____16029  in
        [uu____16028]  in
      uu____15982 :: uu____16025  in
    uu____15932 :: uu____15979  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16137 =
      let uu____16138 =
        let uu____16145 =
          let uu____16146 =
            let uu____16157 =
              let uu____16162 =
                let uu____16165 = FStar_SMTEncoding_Term.boxString b  in
                [uu____16165]  in
              [uu____16162]  in
            let uu____16170 =
              let uu____16171 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16171 tt  in
            (uu____16157, [bb], uu____16170)  in
          FStar_SMTEncoding_Util.mkForall uu____16146  in
        (uu____16145, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16138  in
    let uu____16184 =
      let uu____16187 =
        let uu____16188 =
          let uu____16195 =
            let uu____16196 =
              let uu____16207 =
                let uu____16208 =
                  let uu____16213 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____16213)  in
                FStar_SMTEncoding_Util.mkImp uu____16208  in
              ([[typing_pred]], [xx], uu____16207)  in
            mkForall_fuel uu____16196  in
          (uu____16195, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16188  in
      [uu____16187]  in
    uu____16137 :: uu____16184  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____16268 =
      let uu____16269 =
        let uu____16276 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____16276, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16269  in
    [uu____16268]  in
  let mk_and_interp env conj uu____16292 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16317 =
      let uu____16318 =
        let uu____16325 =
          let uu____16326 =
            let uu____16337 =
              let uu____16338 =
                let uu____16343 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16343, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16338  in
            ([[l_and_a_b]], [aa; bb], uu____16337)  in
          FStar_SMTEncoding_Util.mkForall uu____16326  in
        (uu____16325, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16318  in
    [uu____16317]  in
  let mk_or_interp env disj uu____16379 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16404 =
      let uu____16405 =
        let uu____16412 =
          let uu____16413 =
            let uu____16424 =
              let uu____16425 =
                let uu____16430 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16430, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16425  in
            ([[l_or_a_b]], [aa; bb], uu____16424)  in
          FStar_SMTEncoding_Util.mkForall uu____16413  in
        (uu____16412, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16405  in
    [uu____16404]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16491 =
      let uu____16492 =
        let uu____16499 =
          let uu____16500 =
            let uu____16511 =
              let uu____16512 =
                let uu____16517 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16517, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16512  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16511)  in
          FStar_SMTEncoding_Util.mkForall uu____16500  in
        (uu____16499, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16492  in
    [uu____16491]  in
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
    let uu____16588 =
      let uu____16589 =
        let uu____16596 =
          let uu____16597 =
            let uu____16608 =
              let uu____16609 =
                let uu____16614 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16614, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16609  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16608)  in
          FStar_SMTEncoding_Util.mkForall uu____16597  in
        (uu____16596, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16589  in
    [uu____16588]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16683 =
      let uu____16684 =
        let uu____16691 =
          let uu____16692 =
            let uu____16703 =
              let uu____16704 =
                let uu____16709 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16709, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16704  in
            ([[l_imp_a_b]], [aa; bb], uu____16703)  in
          FStar_SMTEncoding_Util.mkForall uu____16692  in
        (uu____16691, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16684  in
    [uu____16683]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16770 =
      let uu____16771 =
        let uu____16778 =
          let uu____16779 =
            let uu____16790 =
              let uu____16791 =
                let uu____16796 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16796, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16791  in
            ([[l_iff_a_b]], [aa; bb], uu____16790)  in
          FStar_SMTEncoding_Util.mkForall uu____16779  in
        (uu____16778, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16771  in
    [uu____16770]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____16846 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16846  in
    let uu____16849 =
      let uu____16850 =
        let uu____16857 =
          let uu____16858 =
            let uu____16869 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16869)  in
          FStar_SMTEncoding_Util.mkForall uu____16858  in
        (uu____16857, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16850  in
    [uu____16849]  in
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
      let uu____16927 =
        let uu____16934 =
          let uu____16937 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16937]  in
        ("Valid", uu____16934)  in
      FStar_SMTEncoding_Util.mkApp uu____16927  in
    let uu____16940 =
      let uu____16941 =
        let uu____16948 =
          let uu____16949 =
            let uu____16960 =
              let uu____16961 =
                let uu____16966 =
                  let uu____16967 =
                    let uu____16978 =
                      let uu____16983 =
                        let uu____16986 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16986]  in
                      [uu____16983]  in
                    let uu____16991 =
                      let uu____16992 =
                        let uu____16997 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16997, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16992  in
                    (uu____16978, [xx1], uu____16991)  in
                  FStar_SMTEncoding_Util.mkForall uu____16967  in
                (uu____16966, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16961  in
            ([[l_forall_a_b]], [aa; bb], uu____16960)  in
          FStar_SMTEncoding_Util.mkForall uu____16949  in
        (uu____16948, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16941  in
    [uu____16940]  in
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
      let uu____17071 =
        let uu____17078 =
          let uu____17081 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17081]  in
        ("Valid", uu____17078)  in
      FStar_SMTEncoding_Util.mkApp uu____17071  in
    let uu____17084 =
      let uu____17085 =
        let uu____17092 =
          let uu____17093 =
            let uu____17104 =
              let uu____17105 =
                let uu____17110 =
                  let uu____17111 =
                    let uu____17122 =
                      let uu____17127 =
                        let uu____17130 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17130]  in
                      [uu____17127]  in
                    let uu____17135 =
                      let uu____17136 =
                        let uu____17141 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17141, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17136  in
                    (uu____17122, [xx1], uu____17135)  in
                  FStar_SMTEncoding_Util.mkExists uu____17111  in
                (uu____17110, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17105  in
            ([[l_exists_a_b]], [aa; bb], uu____17104)  in
          FStar_SMTEncoding_Util.mkForall uu____17093  in
        (uu____17092, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17085  in
    [uu____17084]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____17193 =
      let uu____17194 =
        let uu____17201 =
          let uu____17202 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____17202 range_ty  in
        let uu____17203 = varops.mk_unique "typing_range_const"  in
        (uu____17201, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____17203)
         in
      FStar_SMTEncoding_Util.mkAssume uu____17194  in
    [uu____17193]  in
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
        let uu____17241 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17241 x1 t  in
      let uu____17242 =
        let uu____17253 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____17253)  in
      FStar_SMTEncoding_Util.mkForall uu____17242  in
    let uu____17270 =
      let uu____17271 =
        let uu____17278 =
          let uu____17279 =
            let uu____17290 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____17290)  in
          FStar_SMTEncoding_Util.mkForall uu____17279  in
        (uu____17278,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17271  in
    [uu____17270]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17338 =
      let uu____17339 =
        let uu____17346 =
          let uu____17347 =
            let uu____17362 =
              let uu____17363 =
                let uu____17368 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17369 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17368, uu____17369)  in
              FStar_SMTEncoding_Util.mkAnd uu____17363  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17362)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17347  in
        (uu____17346,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17339  in
    [uu____17338]  in
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
          let uu____17861 =
            FStar_Util.find_opt
              (fun uu____17897  ->
                 match uu____17897 with
                 | (l,uu____17911) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____17861 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17951,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____18008 = encode_function_type_as_formula t env  in
        match uu____18008 with
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
              let uu____18058 =
                ((let uu____18061 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____18061) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____18058
              then
                let arg_sorts =
                  let uu____18071 =
                    let uu____18072 = FStar_Syntax_Subst.compress t_norm  in
                    uu____18072.FStar_Syntax_Syntax.n  in
                  match uu____18071 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____18078) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____18108  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____18113 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____18115 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____18115 with
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
                (let uu____18144 = prims.is lid  in
                 if uu____18144
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____18152 = prims.mk lid vname  in
                   match uu____18152 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____18179 =
                      let uu____18196 = curried_arrow_formals_comp t_norm  in
                      match uu____18196 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____18238 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____18238
                            then
                              let uu____18239 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___122_18242 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___122_18242.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___122_18242.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___122_18242.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___122_18242.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___122_18242.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___122_18242.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___122_18242.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___122_18242.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___122_18242.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___122_18242.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___122_18242.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___122_18242.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___122_18242.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___122_18242.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___122_18242.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___122_18242.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___122_18242.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___122_18242.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___122_18242.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___122_18242.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___122_18242.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___122_18242.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___122_18242.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___122_18242.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___122_18242.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___122_18242.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___122_18242.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___122_18242.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___122_18242.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___122_18242.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___122_18242.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___122_18242.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___122_18242.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___122_18242.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___122_18242.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___122_18242.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___122_18242.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____18239
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____18260 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____18260)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____18179 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____18334 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____18334 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____18359 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___96_18403  ->
                                       match uu___96_18403 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____18407 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18407 with
                                            | (uu____18428,(xxsym,uu____18430))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____18448 =
                                                  let uu____18449 =
                                                    let uu____18456 =
                                                      let uu____18457 =
                                                        let uu____18468 =
                                                          let uu____18469 =
                                                            let uu____18474 =
                                                              let uu____18475
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____18475
                                                               in
                                                            (vapp,
                                                              uu____18474)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____18469
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18468)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18457
                                                       in
                                                    (uu____18456,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18449
                                                   in
                                                [uu____18448])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____18486 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18486 with
                                            | (uu____18507,(xxsym,uu____18509))
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
                                                let uu____18532 =
                                                  let uu____18533 =
                                                    let uu____18540 =
                                                      let uu____18541 =
                                                        let uu____18552 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18552)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18541
                                                       in
                                                    (uu____18540,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18533
                                                   in
                                                [uu____18532])
                                       | uu____18561 -> []))
                                in
                             let uu____18562 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____18562 with
                              | (vars,guards,env',decls1,uu____18589) ->
                                  let uu____18602 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18615 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18615, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18617 =
                                          encode_formula p env'  in
                                        (match uu____18617 with
                                         | (g,ds) ->
                                             let uu____18630 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____18630,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18602 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____18647 =
                                           let uu____18654 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____18654)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____18647
                                          in
                                       let uu____18659 =
                                         let vname_decl =
                                           let uu____18667 =
                                             let uu____18678 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____18694  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____18678,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____18667
                                            in
                                         let uu____18701 =
                                           let env2 =
                                             let uu___123_18707 = env1  in
                                             {
                                               bindings =
                                                 (uu___123_18707.bindings);
                                               depth = (uu___123_18707.depth);
                                               tcenv = (uu___123_18707.tcenv);
                                               warn = (uu___123_18707.warn);
                                               cache = (uu___123_18707.cache);
                                               nolabels =
                                                 (uu___123_18707.nolabels);
                                               use_zfuel_name =
                                                 (uu___123_18707.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___123_18707.current_module_name)
                                             }  in
                                           let uu____18708 =
                                             let uu____18709 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____18709
                                              in
                                           if uu____18708
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____18701 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____18724::uu____18725 ->
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
                                                     let uu____18765 =
                                                       let uu____18776 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____18776)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____18765
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____18795 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____18802 =
                                               match formals with
                                               | [] ->
                                                   let uu____18819 =
                                                     let uu____18820 =
                                                       let uu____18823 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____18823
                                                        in
                                                     replace_free_var env1
                                                       lid arity vname
                                                       uu____18820
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____18819)
                                               | uu____18832 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____18843 =
                                                       let uu____18850 =
                                                         let uu____18851 =
                                                           let uu____18862 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____18862)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____18851
                                                          in
                                                       (uu____18850,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____18843
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____18802 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____18659 with
                                        | (decls2,env2) ->
                                            let uu____18901 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____18909 =
                                                encode_term res_t1 env'  in
                                              match uu____18909 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____18922 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____18922, decls)
                                               in
                                            (match uu____18901 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____18933 =
                                                     let uu____18940 =
                                                       let uu____18941 =
                                                         let uu____18952 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____18952)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____18941
                                                        in
                                                     (uu____18940,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____18933
                                                    in
                                                 let freshness =
                                                   let uu____18964 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____18964
                                                   then
                                                     let uu____18969 =
                                                       let uu____18970 =
                                                         let uu____18981 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____18996 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____18981,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____18996)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____18970
                                                        in
                                                     let uu____18999 =
                                                       let uu____19002 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____19002]  in
                                                     uu____18969 ::
                                                       uu____18999
                                                   else []  in
                                                 let g =
                                                   let uu____19007 =
                                                     let uu____19010 =
                                                       let uu____19013 =
                                                         let uu____19016 =
                                                           let uu____19019 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____19019
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____19016
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____19013
                                                        in
                                                     FStar_List.append decls2
                                                       uu____19010
                                                      in
                                                   FStar_List.append decls11
                                                     uu____19007
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
          let uu____19052 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19052 with
          | FStar_Pervasives_Native.None  ->
              let uu____19063 = encode_free_var false env x t t_norm []  in
              (match uu____19063 with
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
            let uu____19126 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____19126 with
            | (decls,env1) ->
                let uu____19145 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____19145
                then
                  let uu____19152 =
                    let uu____19155 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____19155  in
                  (uu____19152, env1)
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
             (fun uu____19213  ->
                fun lb  ->
                  match uu____19213 with
                  | (decls,env1) ->
                      let uu____19233 =
                        let uu____19240 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____19240
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____19233 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____19263 = FStar_Syntax_Util.head_and_args t  in
    match uu____19263 with
    | (hd1,args) ->
        let uu____19300 =
          let uu____19301 = FStar_Syntax_Util.un_uinst hd1  in
          uu____19301.FStar_Syntax_Syntax.n  in
        (match uu____19300 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____19305,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____19324 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____19352  ->
      fun quals  ->
        match uu____19352 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____19436 = FStar_Util.first_N nbinders formals  in
              match uu____19436 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19517  ->
                         fun uu____19518  ->
                           match (uu____19517, uu____19518) with
                           | ((formal,uu____19536),(binder,uu____19538)) ->
                               let uu____19547 =
                                 let uu____19554 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19554)  in
                               FStar_Syntax_Syntax.NT uu____19547) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19566 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19597  ->
                              match uu____19597 with
                              | (x,i) ->
                                  let uu____19608 =
                                    let uu___124_19609 = x  in
                                    let uu____19610 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___124_19609.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___124_19609.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19610
                                    }  in
                                  (uu____19608, i)))
                       in
                    FStar_All.pipe_right uu____19566
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19628 =
                      let uu____19633 = FStar_Syntax_Subst.compress body  in
                      let uu____19634 =
                        let uu____19635 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____19635
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____19633
                        uu____19634
                       in
                    uu____19628 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____19704 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____19704
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___125_19707 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___125_19707.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___125_19707.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___125_19707.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___125_19707.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___125_19707.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___125_19707.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___125_19707.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___125_19707.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___125_19707.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___125_19707.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___125_19707.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___125_19707.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___125_19707.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___125_19707.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___125_19707.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___125_19707.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___125_19707.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___125_19707.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___125_19707.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___125_19707.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___125_19707.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___125_19707.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___125_19707.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___125_19707.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___125_19707.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___125_19707.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___125_19707.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___125_19707.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___125_19707.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___125_19707.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___125_19707.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___125_19707.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___125_19707.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___125_19707.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___125_19707.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___125_19707.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___125_19707.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____19732 = FStar_Syntax_Util.abs_formals e  in
                match uu____19732 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____19772::uu____19773 ->
                         let uu____19788 =
                           let uu____19789 =
                             let uu____19792 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____19792
                              in
                           uu____19789.FStar_Syntax_Syntax.n  in
                         (match uu____19788 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19825 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____19825 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____19855 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____19855
                                   then
                                     let uu____19878 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____19878 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19960  ->
                                                   fun uu____19961  ->
                                                     match (uu____19960,
                                                             uu____19961)
                                                     with
                                                     | ((x,uu____19979),
                                                        (b,uu____19981)) ->
                                                         let uu____19990 =
                                                           let uu____19997 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____19997)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19990)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____20005 =
                                            let uu____20028 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____20028)
                                             in
                                          (uu____20005, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____20088 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____20088 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____20165) ->
                              let uu____20170 =
                                let uu____20179 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____20179  in
                              (uu____20170, true)
                          | uu____20208 when Prims.op_Negation norm1 ->
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
                          | uu____20210 ->
                              let uu____20211 =
                                let uu____20212 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____20213 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____20212
                                  uu____20213
                                 in
                              failwith uu____20211)
                     | uu____20226 ->
                         let rec aux' t_norm2 =
                           let uu____20257 =
                             let uu____20258 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____20258.FStar_Syntax_Syntax.n  in
                           match uu____20257 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____20303 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____20303 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____20335 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____20335 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20419)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20424 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20480 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20480
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20492 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____20555  ->
                            fun lb  ->
                              match uu____20555 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____20610 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____20610
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____20613 =
                                      let uu____20622 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____20622
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____20613 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____20492 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____20747 =
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
                        | uu____20753 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20761 = mk_fv ()  in
                                   mk_Apply uu____20761 vars)
                            else
                              (let uu____20763 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____20763)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20823;
                             FStar_Syntax_Syntax.lbeff = uu____20824;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____20826;
                             FStar_Syntax_Syntax.lbpos = uu____20827;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____20851 =
                              let uu____20858 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____20858 with
                              | (tcenv',uu____20874,e_t) ->
                                  let uu____20880 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20891 -> failwith "Impossible"
                                     in
                                  (match uu____20880 with
                                   | (e1,t_norm1) ->
                                       ((let uu___128_20907 = env2  in
                                         {
                                           bindings =
                                             (uu___128_20907.bindings);
                                           depth = (uu___128_20907.depth);
                                           tcenv = tcenv';
                                           warn = (uu___128_20907.warn);
                                           cache = (uu___128_20907.cache);
                                           nolabels =
                                             (uu___128_20907.nolabels);
                                           use_zfuel_name =
                                             (uu___128_20907.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___128_20907.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___128_20907.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____20851 with
                             | (env',e1,t_norm1) ->
                                 let uu____20917 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____20917 with
                                  | ((binders,body,uu____20938,t_body),curry)
                                      ->
                                      ((let uu____20950 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____20950
                                        then
                                          let uu____20951 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____20952 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20951 uu____20952
                                        else ());
                                       (let uu____20954 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____20954 with
                                        | (vars,guards,env'1,binder_decls,uu____20981)
                                            ->
                                            let body1 =
                                              let uu____20995 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____20995
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
                                              let uu____21014 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____21014 curry fvb
                                                vars
                                               in
                                            let uu____21015 =
                                              let uu____21026 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____21026
                                              then
                                                let uu____21039 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____21040 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____21039, uu____21040)
                                              else
                                                (let uu____21050 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____21050))
                                               in
                                            (match uu____21015 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____21079 =
                                                     let uu____21086 =
                                                       let uu____21087 =
                                                         let uu____21098 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____21098)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____21087
                                                        in
                                                     let uu____21107 =
                                                       let uu____21108 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21108
                                                        in
                                                     (uu____21086,
                                                       uu____21107,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____21079
                                                    in
                                                 let uu____21109 =
                                                   let uu____21112 =
                                                     let uu____21115 =
                                                       let uu____21118 =
                                                         let uu____21121 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____21121
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____21118
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____21115
                                                      in
                                                   FStar_List.append decls1
                                                     uu____21112
                                                    in
                                                 (uu____21109, env2))))))
                        | uu____21126 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____21189 = varops.fresh "fuel"  in
                          (uu____21189, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21192 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____21239  ->
                                  fun fvb  ->
                                    match uu____21239 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____21285 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21285  in
                                        let gtok =
                                          let uu____21287 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21287  in
                                        let env4 =
                                          let uu____21289 =
                                            let uu____21292 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____21292
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____21289
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____21192 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21398 t_norm
                              uu____21400 =
                              match (uu____21398, uu____21400) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____21428;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____21429;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____21431;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____21432;_})
                                  ->
                                  let uu____21453 =
                                    let uu____21460 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21460 with
                                    | (tcenv',uu____21476,e_t) ->
                                        let uu____21482 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21493 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21482 with
                                         | (e1,t_norm1) ->
                                             ((let uu___129_21509 = env3  in
                                               {
                                                 bindings =
                                                   (uu___129_21509.bindings);
                                                 depth =
                                                   (uu___129_21509.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___129_21509.warn);
                                                 cache =
                                                   (uu___129_21509.cache);
                                                 nolabels =
                                                   (uu___129_21509.nolabels);
                                                 use_zfuel_name =
                                                   (uu___129_21509.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___129_21509.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___129_21509.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21453 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21524 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21524
                                         then
                                           let uu____21525 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21526 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21527 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21525 uu____21526
                                             uu____21527
                                         else ());
                                        (let uu____21529 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____21529 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21566 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____21566
                                               then
                                                 let uu____21567 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____21568 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____21569 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____21570 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21567 uu____21568
                                                   uu____21569 uu____21570
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21574 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____21574 with
                                               | (vars,guards,env'1,binder_decls,uu____21605)
                                                   ->
                                                   let decl_g =
                                                     let uu____21619 =
                                                       let uu____21630 =
                                                         let uu____21633 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21633
                                                          in
                                                       (g, uu____21630,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21619
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
                                                     let uu____21646 =
                                                       let uu____21653 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____21653)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21646
                                                      in
                                                   let gsapp =
                                                     let uu____21659 =
                                                       let uu____21666 =
                                                         let uu____21669 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____21669 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21666)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21659
                                                      in
                                                   let gmax =
                                                     let uu____21675 =
                                                       let uu____21682 =
                                                         let uu____21685 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____21685 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21682)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21675
                                                      in
                                                   let body1 =
                                                     let uu____21691 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____21691
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____21693 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____21693 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21711 =
                                                            let uu____21718 =
                                                              let uu____21719
                                                                =
                                                                let uu____21734
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
                                                                  uu____21734)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21719
                                                               in
                                                            let uu____21745 =
                                                              let uu____21746
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21746
                                                               in
                                                            (uu____21718,
                                                              uu____21745,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21711
                                                           in
                                                        let eqn_f =
                                                          let uu____21748 =
                                                            let uu____21755 =
                                                              let uu____21756
                                                                =
                                                                let uu____21767
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21767)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21756
                                                               in
                                                            (uu____21755,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21748
                                                           in
                                                        let eqn_g' =
                                                          let uu____21777 =
                                                            let uu____21784 =
                                                              let uu____21785
                                                                =
                                                                let uu____21796
                                                                  =
                                                                  let uu____21797
                                                                    =
                                                                    let uu____21802
                                                                    =
                                                                    let uu____21803
                                                                    =
                                                                    let uu____21810
                                                                    =
                                                                    let uu____21813
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____21813
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____21810)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21803
                                                                     in
                                                                    (gsapp,
                                                                    uu____21802)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21797
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21796)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21785
                                                               in
                                                            (uu____21784,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21777
                                                           in
                                                        let uu____21824 =
                                                          let uu____21833 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____21833
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21862)
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
                                                                  let uu____21883
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____21883
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____21884
                                                                  =
                                                                  let uu____21891
                                                                    =
                                                                    let uu____21892
                                                                    =
                                                                    let uu____21903
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21903)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21892
                                                                     in
                                                                  (uu____21891,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21884
                                                                 in
                                                              let uu____21912
                                                                =
                                                                let uu____21919
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____21919
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21932
                                                                    =
                                                                    let uu____21935
                                                                    =
                                                                    let uu____21936
                                                                    =
                                                                    let uu____21943
                                                                    =
                                                                    let uu____21944
                                                                    =
                                                                    let uu____21955
                                                                    =
                                                                    let uu____21956
                                                                    =
                                                                    let uu____21961
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____21961,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21956
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21955)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21944
                                                                     in
                                                                    (uu____21943,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21936
                                                                     in
                                                                    [uu____21935]
                                                                     in
                                                                    (d3,
                                                                    uu____21932)
                                                                 in
                                                              (match uu____21912
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
                                                        (match uu____21824
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
                            let uu____22014 =
                              let uu____22027 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22084  ->
                                   fun uu____22085  ->
                                     match (uu____22084, uu____22085) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22200 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22200 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22027
                               in
                            (match uu____22014 with
                             | (decls2,eqns,env01) ->
                                 let uu____22273 =
                                   let isDeclFun uu___97_22287 =
                                     match uu___97_22287 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22288 -> true
                                     | uu____22299 -> false  in
                                   let uu____22300 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22300
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22273 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22340 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___98_22344  ->
                                 match uu___98_22344 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22345 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22351 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22351)))
                         in
                      if uu____22340
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
                   let uu____22403 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22403
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
        let uu____22464 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22464 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22468 = encode_sigelt' env se  in
      match uu____22468 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22480 =
                  let uu____22481 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22481  in
                [uu____22480]
            | uu____22482 ->
                let uu____22483 =
                  let uu____22486 =
                    let uu____22487 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22487  in
                  uu____22486 :: g  in
                let uu____22488 =
                  let uu____22491 =
                    let uu____22492 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22492  in
                  [uu____22491]  in
                FStar_List.append uu____22483 uu____22488
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
        let uu____22505 =
          let uu____22506 = FStar_Syntax_Subst.compress t  in
          uu____22506.FStar_Syntax_Syntax.n  in
        match uu____22505 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22510)) -> s = "opaque_to_smt"
        | uu____22511 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22518 =
          let uu____22519 = FStar_Syntax_Subst.compress t  in
          uu____22519.FStar_Syntax_Syntax.n  in
        match uu____22518 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22523)) -> s = "uninterpreted_by_smt"
        | uu____22524 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22529 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____22534 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22545 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22546 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22547 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22560 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22562 =
            let uu____22563 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____22563 Prims.op_Negation  in
          if uu____22562
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22589 ->
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
               let uu____22619 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____22619 with
               | (formals,uu____22637) ->
                   let arity = FStar_List.length formals  in
                   let uu____22655 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____22655 with
                    | (aname,atok,env2) ->
                        let uu____22675 =
                          let uu____22680 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____22680 env2  in
                        (match uu____22675 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22692 =
                                 let uu____22693 =
                                   let uu____22704 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22720  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____22704,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____22693
                                  in
                               [uu____22692;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____22729 =
                               let aux uu____22785 uu____22786 =
                                 match (uu____22785, uu____22786) with
                                 | ((bv,uu____22838),(env3,acc_sorts,acc)) ->
                                     let uu____22876 = gen_term_var env3 bv
                                        in
                                     (match uu____22876 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____22729 with
                              | (uu____22948,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____22971 =
                                      let uu____22978 =
                                        let uu____22979 =
                                          let uu____22990 =
                                            let uu____22991 =
                                              let uu____22996 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____22996)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22991
                                             in
                                          ([[app]], xs_sorts, uu____22990)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22979
                                         in
                                      (uu____22978,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22971
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23008 =
                                      let uu____23015 =
                                        let uu____23016 =
                                          let uu____23027 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23027)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23016
                                         in
                                      (uu____23015,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23008
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23038 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23038 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23064,uu____23065)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23066 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____23066 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23081,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23087 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___99_23091  ->
                      match uu___99_23091 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23092 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23097 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23098 -> false))
               in
            Prims.op_Negation uu____23087  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23105 =
               let uu____23112 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23112 env fv t quals  in
             match uu____23105 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23127 =
                   let uu____23128 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23128  in
                 (uu____23127, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23134 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23134 with
           | (uu____23143,f1) ->
               let uu____23145 = encode_formula f1 env  in
               (match uu____23145 with
                | (f2,decls) ->
                    let g =
                      let uu____23159 =
                        let uu____23160 =
                          let uu____23167 =
                            let uu____23168 =
                              let uu____23169 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23169
                               in
                            FStar_Pervasives_Native.Some uu____23168  in
                          let uu____23170 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23167, uu____23170)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23160  in
                      [uu____23159]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23172) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23184 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23202 =
                       let uu____23205 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23205.FStar_Syntax_Syntax.fv_name  in
                     uu____23202.FStar_Syntax_Syntax.v  in
                   let uu____23206 =
                     let uu____23207 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23207  in
                   if uu____23206
                   then
                     let val_decl =
                       let uu___132_23235 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___132_23235.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___132_23235.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___132_23235.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23236 = encode_sigelt' env1 val_decl  in
                     match uu____23236 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23184 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23260,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23262;
                          FStar_Syntax_Syntax.lbtyp = uu____23263;
                          FStar_Syntax_Syntax.lbeff = uu____23264;
                          FStar_Syntax_Syntax.lbdef = uu____23265;
                          FStar_Syntax_Syntax.lbattrs = uu____23266;
                          FStar_Syntax_Syntax.lbpos = uu____23267;_}::[]),uu____23268)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23285 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____23285 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23314 =
                   let uu____23317 =
                     let uu____23318 =
                       let uu____23325 =
                         let uu____23326 =
                           let uu____23337 =
                             let uu____23338 =
                               let uu____23343 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23343)  in
                             FStar_SMTEncoding_Util.mkEq uu____23338  in
                           ([[b2t_x]], [xx], uu____23337)  in
                         FStar_SMTEncoding_Util.mkForall uu____23326  in
                       (uu____23325,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23318  in
                   [uu____23317]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23314
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23364,uu____23365) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_23374  ->
                  match uu___100_23374 with
                  | FStar_Syntax_Syntax.Discriminator uu____23375 -> true
                  | uu____23376 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23377,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23388 =
                     let uu____23389 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23389.FStar_Ident.idText  in
                   uu____23388 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___101_23393  ->
                     match uu___101_23393 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23394 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23396) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___102_23407  ->
                  match uu___102_23407 with
                  | FStar_Syntax_Syntax.Projector uu____23408 -> true
                  | uu____23413 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23416 = try_lookup_free_var env l  in
          (match uu____23416 with
           | FStar_Pervasives_Native.Some uu____23423 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___133_23425 = se  in
                 let uu____23426 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____23426;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_23425.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_23425.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___133_23425.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23429) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23441) ->
          let uu____23450 = encode_sigelts env ses  in
          (match uu____23450 with
           | (g,env1) ->
               let uu____23467 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___103_23490  ->
                         match uu___103_23490 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23491;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23492;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23493;_}
                             -> false
                         | uu____23496 -> true))
                  in
               (match uu____23467 with
                | (g',inversions) ->
                    let uu____23511 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___104_23532  ->
                              match uu___104_23532 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23533 ->
                                  true
                              | uu____23544 -> false))
                       in
                    (match uu____23511 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23560,tps,k,uu____23563,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___105_23580  ->
                    match uu___105_23580 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23581 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23588 = c  in
              match uu____23588 with
              | (name,args,uu____23591,uu____23592,uu____23593) ->
                  let uu____23598 =
                    let uu____23599 =
                      let uu____23610 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23633  ->
                                match uu____23633 with
                                | (uu____23640,sort,uu____23642) -> sort))
                         in
                      (name, uu____23610, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____23599  in
                  [uu____23598]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____23671 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23677 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____23677 FStar_Option.isNone))
               in
            if uu____23671
            then []
            else
              (let uu____23709 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____23709 with
               | (xxsym,xx) ->
                   let uu____23718 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23757  ->
                             fun l  ->
                               match uu____23757 with
                               | (out,decls) ->
                                   let uu____23777 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____23777 with
                                    | (uu____23788,data_t) ->
                                        let uu____23790 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____23790 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23828 =
                                                 let uu____23829 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____23829.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____23828 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23832,indices) ->
                                                   indices
                                               | uu____23854 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23878  ->
                                                         match uu____23878
                                                         with
                                                         | (x,uu____23884) ->
                                                             let uu____23885
                                                               =
                                                               let uu____23886
                                                                 =
                                                                 let uu____23893
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23893,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23886
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____23885)
                                                    env)
                                                in
                                             let uu____23896 =
                                               encode_args indices env1  in
                                             (match uu____23896 with
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
                                                      let uu____23922 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23938
                                                                 =
                                                                 let uu____23943
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23943,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23938)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23922
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23946 =
                                                      let uu____23947 =
                                                        let uu____23952 =
                                                          let uu____23953 =
                                                            let uu____23958 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23958,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23953
                                                           in
                                                        (out, uu____23952)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23947
                                                       in
                                                    (uu____23946,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____23718 with
                    | (data_ax,decls) ->
                        let uu____23971 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23971 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23982 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23982 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23986 =
                                 let uu____23993 =
                                   let uu____23994 =
                                     let uu____24005 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24014 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24005,
                                       uu____24014)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23994
                                    in
                                 let uu____24023 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23993,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24023)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23986
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24024 =
            let uu____24029 =
              let uu____24030 = FStar_Syntax_Subst.compress k  in
              uu____24030.FStar_Syntax_Syntax.n  in
            match uu____24029 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24067 -> (tps, k)  in
          (match uu____24024 with
           | (formals,res) ->
               let uu____24074 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24074 with
                | (formals1,res1) ->
                    let uu____24085 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24085 with
                     | (vars,guards,env',binder_decls,uu____24110) ->
                         let arity = FStar_List.length vars  in
                         let uu____24124 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____24124 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24147 =
                                  let uu____24154 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24154)  in
                                FStar_SMTEncoding_Util.mkApp uu____24147  in
                              let uu____24159 =
                                let tname_decl =
                                  let uu____24167 =
                                    let uu____24168 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24192  ->
                                              match uu____24192 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24205 = varops.next_id ()  in
                                    (tname, uu____24168,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24205, false)
                                     in
                                  constructor_or_logic_type_decl uu____24167
                                   in
                                let uu____24208 =
                                  match vars with
                                  | [] ->
                                      let uu____24221 =
                                        let uu____24222 =
                                          let uu____24225 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____24225
                                           in
                                        replace_free_var env1 t arity tname
                                          uu____24222
                                         in
                                      ([], uu____24221)
                                  | uu____24236 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24243 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24243
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24257 =
                                          let uu____24264 =
                                            let uu____24265 =
                                              let uu____24280 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24280)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24265
                                             in
                                          (uu____24264,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24257
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24208 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24159 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24316 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24316 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24334 =
                                               let uu____24335 =
                                                 let uu____24342 =
                                                   let uu____24343 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24343
                                                    in
                                                 (uu____24342,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24335
                                                in
                                             [uu____24334]
                                           else []  in
                                         let uu____24345 =
                                           let uu____24348 =
                                             let uu____24351 =
                                               let uu____24352 =
                                                 let uu____24359 =
                                                   let uu____24360 =
                                                     let uu____24371 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24371)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24360
                                                    in
                                                 (uu____24359,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24352
                                                in
                                             [uu____24351]  in
                                           FStar_List.append karr uu____24348
                                            in
                                         FStar_List.append decls1 uu____24345
                                      in
                                   let aux =
                                     let uu____24383 =
                                       let uu____24386 =
                                         inversion_axioms tapp vars  in
                                       let uu____24389 =
                                         let uu____24392 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24392]  in
                                       FStar_List.append uu____24386
                                         uu____24389
                                        in
                                     FStar_List.append kindingAx uu____24383
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24397,uu____24398,uu____24399,uu____24400,uu____24401)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24407,t,uu____24409,n_tps,uu____24411) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24419 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____24419 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____24459 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____24459 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____24480 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24480 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____24494 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____24494 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____24552 =
                                            mk_term_projector_name d x  in
                                          (uu____24552,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____24556 =
                                  let uu____24557 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24557, true)
                                   in
                                FStar_All.pipe_right uu____24556
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
                              let uu____24570 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____24570 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24582::uu____24583 ->
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
                                         let uu____24610 =
                                           let uu____24621 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24621)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24610
                                     | uu____24640 -> tok_typing  in
                                   let uu____24643 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____24643 with
                                    | (vars',guards',env'',decls_formals,uu____24668)
                                        ->
                                        let uu____24681 =
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
                                        (match uu____24681 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24708 ->
                                                   let uu____24715 =
                                                     let uu____24716 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24716
                                                      in
                                                   [uu____24715]
                                                in
                                             let encode_elim uu____24728 =
                                               let uu____24729 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24729 with
                                               | (head1,args) ->
                                                   let uu____24772 =
                                                     let uu____24773 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24773.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24772 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24783;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24784;_},uu____24785)
                                                        ->
                                                        let uu____24790 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24790
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24803
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24803
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
                                                                    uu____24852
                                                                    ->
                                                                    let uu____24853
                                                                    =
                                                                    let uu____24858
                                                                    =
                                                                    let uu____24859
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24859
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24858)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24853
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24875
                                                                    =
                                                                    let uu____24876
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24876
                                                                     in
                                                                    if
                                                                    uu____24875
                                                                    then
                                                                    let uu____24889
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24889]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24891
                                                                    =
                                                                    let uu____24904
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24954
                                                                     ->
                                                                    fun
                                                                    uu____24955
                                                                     ->
                                                                    match 
                                                                    (uu____24954,
                                                                    uu____24955)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25050
                                                                    =
                                                                    let uu____25057
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25057
                                                                     in
                                                                    (match uu____25050
                                                                    with
                                                                    | 
                                                                    (uu____25070,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25078
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25078
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25080
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25080
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
                                                                    uu____24904
                                                                     in
                                                                  (match uu____24891
                                                                   with
                                                                   | 
                                                                   (uu____25095,arg_vars,elim_eqns_or_guards,uu____25098)
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
                                                                    let uu____25122
                                                                    =
                                                                    let uu____25129
                                                                    =
                                                                    let uu____25130
                                                                    =
                                                                    let uu____25141
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25142
                                                                    =
                                                                    let uu____25143
                                                                    =
                                                                    let uu____25148
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25148)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25143
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25141,
                                                                    uu____25142)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25130
                                                                     in
                                                                    (uu____25129,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25122
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____25158
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____25158
                                                                    then
                                                                    let x =
                                                                    let uu____25164
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25164,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25166
                                                                    =
                                                                    let uu____25173
                                                                    =
                                                                    let uu____25174
                                                                    =
                                                                    let uu____25185
                                                                    =
                                                                    let uu____25190
                                                                    =
                                                                    let uu____25193
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25193]
                                                                     in
                                                                    [uu____25190]
                                                                     in
                                                                    let uu____25198
                                                                    =
                                                                    let uu____25199
                                                                    =
                                                                    let uu____25204
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25205
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25204,
                                                                    uu____25205)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25199
                                                                     in
                                                                    (uu____25185,
                                                                    [x],
                                                                    uu____25198)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25174
                                                                     in
                                                                    let uu____25218
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25173,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25218)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25166
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25223
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
                                                                    (let uu____25255
                                                                    =
                                                                    let uu____25256
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25256
                                                                    dapp1  in
                                                                    [uu____25255])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25223
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25263
                                                                    =
                                                                    let uu____25270
                                                                    =
                                                                    let uu____25271
                                                                    =
                                                                    let uu____25282
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25283
                                                                    =
                                                                    let uu____25284
                                                                    =
                                                                    let uu____25289
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25289)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25284
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25282,
                                                                    uu____25283)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25271
                                                                     in
                                                                    (uu____25270,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25263)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____25301 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25301
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25314
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25314
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
                                                                    uu____25363
                                                                    ->
                                                                    let uu____25364
                                                                    =
                                                                    let uu____25369
                                                                    =
                                                                    let uu____25370
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25370
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25369)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25364
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25386
                                                                    =
                                                                    let uu____25387
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25387
                                                                     in
                                                                    if
                                                                    uu____25386
                                                                    then
                                                                    let uu____25400
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25400]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25402
                                                                    =
                                                                    let uu____25415
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25465
                                                                     ->
                                                                    fun
                                                                    uu____25466
                                                                     ->
                                                                    match 
                                                                    (uu____25465,
                                                                    uu____25466)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25561
                                                                    =
                                                                    let uu____25568
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25568
                                                                     in
                                                                    (match uu____25561
                                                                    with
                                                                    | 
                                                                    (uu____25581,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25589
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25589
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25591
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25591
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
                                                                    uu____25415
                                                                     in
                                                                  (match uu____25402
                                                                   with
                                                                   | 
                                                                   (uu____25606,arg_vars,elim_eqns_or_guards,uu____25609)
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
                                                                    let uu____25633
                                                                    =
                                                                    let uu____25640
                                                                    =
                                                                    let uu____25641
                                                                    =
                                                                    let uu____25652
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    let uu____25659
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25659)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25654
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25652,
                                                                    uu____25653)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25641
                                                                     in
                                                                    (uu____25640,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25633
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____25669
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____25669
                                                                    then
                                                                    let x =
                                                                    let uu____25675
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25675,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25677
                                                                    =
                                                                    let uu____25684
                                                                    =
                                                                    let uu____25685
                                                                    =
                                                                    let uu____25696
                                                                    =
                                                                    let uu____25701
                                                                    =
                                                                    let uu____25704
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25704]
                                                                     in
                                                                    [uu____25701]
                                                                     in
                                                                    let uu____25709
                                                                    =
                                                                    let uu____25710
                                                                    =
                                                                    let uu____25715
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25716
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25715,
                                                                    uu____25716)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25710
                                                                     in
                                                                    (uu____25696,
                                                                    [x],
                                                                    uu____25709)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25685
                                                                     in
                                                                    let uu____25729
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25684,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25729)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25677
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25734
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
                                                                    (let uu____25766
                                                                    =
                                                                    let uu____25767
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25767
                                                                    dapp1  in
                                                                    [uu____25766])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25734
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25774
                                                                    =
                                                                    let uu____25781
                                                                    =
                                                                    let uu____25782
                                                                    =
                                                                    let uu____25793
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25794
                                                                    =
                                                                    let uu____25795
                                                                    =
                                                                    let uu____25800
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25800)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25795
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25793,
                                                                    uu____25794)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25782
                                                                     in
                                                                    (uu____25781,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25774)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____25811 ->
                                                        ((let uu____25813 =
                                                            let uu____25818 =
                                                              let uu____25819
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25820
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25819
                                                                uu____25820
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25818)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25813);
                                                         ([], [])))
                                                in
                                             let uu____25825 = encode_elim ()
                                                in
                                             (match uu____25825 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25845 =
                                                      let uu____25848 =
                                                        let uu____25851 =
                                                          let uu____25854 =
                                                            let uu____25857 =
                                                              let uu____25858
                                                                =
                                                                let uu____25869
                                                                  =
                                                                  let uu____25870
                                                                    =
                                                                    let uu____25871
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25871
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25870
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25869)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25858
                                                               in
                                                            [uu____25857]  in
                                                          let uu____25874 =
                                                            let uu____25877 =
                                                              let uu____25880
                                                                =
                                                                let uu____25883
                                                                  =
                                                                  let uu____25886
                                                                    =
                                                                    let uu____25889
                                                                    =
                                                                    let uu____25892
                                                                    =
                                                                    let uu____25893
                                                                    =
                                                                    let uu____25900
                                                                    =
                                                                    let uu____25901
                                                                    =
                                                                    let uu____25912
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25912)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25901
                                                                     in
                                                                    (uu____25900,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25893
                                                                     in
                                                                    let uu____25921
                                                                    =
                                                                    let uu____25924
                                                                    =
                                                                    let uu____25925
                                                                    =
                                                                    let uu____25932
                                                                    =
                                                                    let uu____25933
                                                                    =
                                                                    let uu____25944
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25945
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25944,
                                                                    uu____25945)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25933
                                                                     in
                                                                    (uu____25932,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25925
                                                                     in
                                                                    [uu____25924]
                                                                     in
                                                                    uu____25892
                                                                    ::
                                                                    uu____25921
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25889
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25886
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25883
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25880
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25877
                                                             in
                                                          FStar_List.append
                                                            uu____25854
                                                            uu____25874
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25851
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25848
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25845
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
           (fun uu____25979  ->
              fun se  ->
                match uu____25979 with
                | (g,env1) ->
                    let uu____25999 = encode_sigelt env1 se  in
                    (match uu____25999 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26064 =
        match uu____26064 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____26096 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____26102 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26102
                   then
                     let uu____26103 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26104 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26105 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26103 uu____26104 uu____26105
                   else ());
                  (let uu____26107 = encode_term t1 env1  in
                   match uu____26107 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26123 =
                         let uu____26130 =
                           let uu____26131 =
                             let uu____26132 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26132
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26131  in
                         new_term_constant_from_string env1 x uu____26130  in
                       (match uu____26123 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26146 = FStar_Options.log_queries ()
                                 in
                              if uu____26146
                              then
                                let uu____26147 =
                                  let uu____26148 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26149 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26150 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26148 uu____26149 uu____26150
                                   in
                                FStar_Pervasives_Native.Some uu____26147
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____26162,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26182 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26182 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26205 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26205 with | (uu____26224,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26233 'Auu____26234 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26233,'Auu____26234)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26303  ->
              match uu____26303 with
              | (l,uu____26315,uu____26316) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26360  ->
              match uu____26360 with
              | (l,uu____26374,uu____26375) ->
                  let uu____26384 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26385 =
                    let uu____26388 =
                      let uu____26389 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26389  in
                    [uu____26388]  in
                  uu____26384 :: uu____26385))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____26416 =
      let uu____26419 =
        let uu____26420 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____26423 =
          let uu____26424 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____26424 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26420;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26423
        }  in
      [uu____26419]  in
    FStar_ST.op_Colon_Equals last_env uu____26416
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____26462 = FStar_ST.op_Bang last_env  in
      match uu____26462 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26493 ->
          let uu___134_26496 = e  in
          let uu____26497 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___134_26496.bindings);
            depth = (uu___134_26496.depth);
            tcenv;
            warn = (uu___134_26496.warn);
            cache = (uu___134_26496.cache);
            nolabels = (uu___134_26496.nolabels);
            use_zfuel_name = (uu___134_26496.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_26496.encode_non_total_function_typ);
            current_module_name = uu____26497
          }
  
let (set_env : env_t -> unit) =
  fun env  ->
    let uu____26503 = FStar_ST.op_Bang last_env  in
    match uu____26503 with
    | [] -> failwith "Empty env stack"
    | uu____26533::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____26568  ->
    let uu____26569 = FStar_ST.op_Bang last_env  in
    match uu____26569 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___135_26607 = hd1  in
          {
            bindings = (uu___135_26607.bindings);
            depth = (uu___135_26607.depth);
            tcenv = (uu___135_26607.tcenv);
            warn = (uu___135_26607.warn);
            cache = refs;
            nolabels = (uu___135_26607.nolabels);
            use_zfuel_name = (uu___135_26607.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___135_26607.encode_non_total_function_typ);
            current_module_name = (uu___135_26607.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____26639  ->
    let uu____26640 = FStar_ST.op_Bang last_env  in
    match uu____26640 with
    | [] -> failwith "Popping an empty stack"
    | uu____26670::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____26752::uu____26753,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___136_26761 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___136_26761.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___136_26761.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___136_26761.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26762 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26781 =
        let uu____26784 =
          let uu____26785 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26785  in
        let uu____26786 = open_fact_db_tags env  in uu____26784 ::
          uu____26786
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26781
  
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
      let uu____26812 = encode_sigelt env se  in
      match uu____26812 with
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
        let uu____26856 = FStar_Options.log_queries ()  in
        if uu____26856
        then
          let uu____26859 =
            let uu____26860 =
              let uu____26861 =
                let uu____26862 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26862 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26861  in
            FStar_SMTEncoding_Term.Caption uu____26860  in
          uu____26859 :: decls
        else decls  in
      (let uu____26873 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26873
       then
         let uu____26874 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26874
       else ());
      (let env =
         let uu____26877 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26877 tcenv  in
       let uu____26878 = encode_top_level_facts env se  in
       match uu____26878 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26892 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26892)))
  
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
      (let uu____26908 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26908
       then
         let uu____26909 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26909
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26950  ->
                 fun se  ->
                   match uu____26950 with
                   | (g,env2) ->
                       let uu____26970 = encode_top_level_facts env2 se  in
                       (match uu____26970 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26993 =
         encode_signature
           (let uu___137_27002 = env  in
            {
              bindings = (uu___137_27002.bindings);
              depth = (uu___137_27002.depth);
              tcenv = (uu___137_27002.tcenv);
              warn = false;
              cache = (uu___137_27002.cache);
              nolabels = (uu___137_27002.nolabels);
              use_zfuel_name = (uu___137_27002.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___137_27002.encode_non_total_function_typ);
              current_module_name = (uu___137_27002.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26993 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27021 = FStar_Options.log_queries ()  in
             if uu____27021
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___138_27029 = env1  in
               {
                 bindings = (uu___138_27029.bindings);
                 depth = (uu___138_27029.depth);
                 tcenv = (uu___138_27029.tcenv);
                 warn = true;
                 cache = (uu___138_27029.cache);
                 nolabels = (uu___138_27029.nolabels);
                 use_zfuel_name = (uu___138_27029.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___138_27029.encode_non_total_function_typ);
                 current_module_name = (uu___138_27029.current_module_name)
               });
            (let uu____27031 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____27031
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
        (let uu____27089 =
           let uu____27090 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____27090.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27089);
        (let env =
           let uu____27092 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____27092 tcenv  in
         let uu____27093 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____27130 = aux rest  in
                 (match uu____27130 with
                  | (out,rest1) ->
                      let t =
                        let uu____27158 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27158 with
                        | FStar_Pervasives_Native.Some uu____27161 ->
                            let uu____27162 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27162
                              x.FStar_Syntax_Syntax.sort
                        | uu____27163 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27167 =
                        let uu____27170 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___139_27173 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___139_27173.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___139_27173.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27170 :: out  in
                      (uu____27167, rest1))
             | uu____27178 -> ([], bindings)  in
           let uu____27185 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____27185 with
           | (closing,bindings) ->
               let uu____27210 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27210, bindings)
            in
         match uu____27093 with
         | (q1,bindings) ->
             let uu____27233 = encode_env_bindings env bindings  in
             (match uu____27233 with
              | (env_decls,env1) ->
                  ((let uu____27255 =
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
                    if uu____27255
                    then
                      let uu____27256 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27256
                    else ());
                   (let uu____27258 = encode_formula q1 env1  in
                    match uu____27258 with
                    | (phi,qdecls) ->
                        let uu____27279 =
                          let uu____27284 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27284 phi
                           in
                        (match uu____27279 with
                         | (labels,phi1) ->
                             let uu____27301 = encode_labels labels  in
                             (match uu____27301 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27338 =
                                      let uu____27345 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27346 =
                                        varops.mk_unique "@query"  in
                                      (uu____27345,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27346)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27338
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
  