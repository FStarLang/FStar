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
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
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
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4156) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4161 ->
        let uu____4162 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4162)
  
let is_arithmetic_primitive :
  'Auu____4179 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4179 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4201::uu____4202::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4206::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4209 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4232 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4249 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4256 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4256)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4297)::uu____4298::uu____4299::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4350)::uu____4351::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4388 -> false
  
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
          let uu____4697 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4697, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4700 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4700, [])
      | FStar_Const.Const_char c1 ->
          let uu____4704 =
            let uu____4705 =
              let uu____4712 =
                let uu____4715 =
                  let uu____4716 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4716  in
                [uu____4715]  in
              ("FStar.Char.__char_of_int", uu____4712)  in
            FStar_SMTEncoding_Util.mkApp uu____4705  in
          (uu____4704, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4732 =
            let uu____4733 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4733  in
          (uu____4732, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4754) ->
          let uu____4755 = varops.string_const s  in (uu____4755, [])
      | FStar_Const.Const_range uu____4758 ->
          let uu____4759 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4759, [])
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
        (let uu____4795 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4795
         then
           let uu____4796 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4796
         else ());
        (let uu____4798 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4888  ->
                   fun b  ->
                     match uu____4888 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4967 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4983 = gen_term_var env1 x  in
                           match uu____4983 with
                           | (xxsym,xx,env') ->
                               let uu____5007 =
                                 let uu____5012 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____5012 env1 xx
                                  in
                               (match uu____5007 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4967 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4798 with
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
          let uu____5161 = encode_term t env  in
          match uu____5161 with
          | (t1,decls) ->
              let uu____5172 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5172, decls)

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
          let uu____5183 = encode_term t env  in
          match uu____5183 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5198 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5198, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5200 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5200, decls))

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
        let uu____5206 = encode_args args_e env  in
        match uu____5206 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5225 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5236 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5236  in
            let binary arg_tms1 =
              let uu____5251 =
                let uu____5252 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5252  in
              let uu____5253 =
                let uu____5254 =
                  let uu____5255 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5255  in
                FStar_SMTEncoding_Term.unboxInt uu____5254  in
              (uu____5251, uu____5253)  in
            let mk_default uu____5263 =
              let uu____5264 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5264 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____5326 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5326
              then
                let uu____5327 =
                  let uu____5328 = mk_args ts  in op uu____5328  in
                FStar_All.pipe_right uu____5327 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5363 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5363
              then
                let uu____5364 = binary ts  in
                match uu____5364 with
                | (t1,t2) ->
                    let uu____5371 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5371
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5375 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5375
                 then
                   let uu____5376 =
                     let uu____5377 = binary ts  in op uu____5377  in
                   FStar_All.pipe_right uu____5376
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
            let uu____5538 =
              let uu____5548 =
                FStar_List.tryFind
                  (fun uu____5572  ->
                     match uu____5572 with
                     | (l,uu____5582) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5548 FStar_Util.must  in
            (match uu____5538 with
             | (uu____5626,op) ->
                 let uu____5638 = op arg_tms  in (uu____5638, decls))

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
        let uu____5652 = FStar_List.hd args_e  in
        match uu____5652 with
        | (tm_sz,uu____5666) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5676 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5676 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____5684 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5684);
                   t_decls1)
               in
            let uu____5685 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5723::(sz_arg,uu____5725)::uu____5726::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5775 =
                    let uu____5784 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5784  in
                  let uu____5805 =
                    let uu____5808 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5808  in
                  (uu____5775, uu____5805)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5820::(sz_arg,uu____5822)::uu____5823::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5872 =
                    let uu____5873 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5873
                     in
                  failwith uu____5872
              | uu____5888 ->
                  let uu____5901 = FStar_List.tail args_e  in
                  (uu____5901, FStar_Pervasives_Native.None)
               in
            (match uu____5685 with
             | (arg_tms,ext_sz) ->
                 let uu____5954 = encode_args arg_tms env  in
                 (match uu____5954 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5975 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5986 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5986  in
                      let unary_arith arg_tms2 =
                        let uu____5997 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5997  in
                      let binary arg_tms2 =
                        let uu____6012 =
                          let uu____6013 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____6013
                           in
                        let uu____6014 =
                          let uu____6015 =
                            let uu____6016 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____6016  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____6015
                           in
                        (uu____6012, uu____6014)  in
                      let binary_arith arg_tms2 =
                        let uu____6033 =
                          let uu____6034 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____6034
                           in
                        let uu____6035 =
                          let uu____6036 =
                            let uu____6037 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____6037  in
                          FStar_SMTEncoding_Term.unboxInt uu____6036  in
                        (uu____6033, uu____6035)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____6095 =
                          let uu____6096 = mk_args ts  in op uu____6096  in
                        FStar_All.pipe_right uu____6095 resBox  in
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
                        let uu____6228 =
                          let uu____6233 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____6233  in
                        let uu____6235 =
                          let uu____6240 =
                            let uu____6241 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____6241  in
                          FStar_SMTEncoding_Term.boxBitVec uu____6240  in
                        mk_bv uu____6228 unary uu____6235 arg_tms2  in
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
                      let uu____6474 =
                        let uu____6484 =
                          FStar_List.tryFind
                            (fun uu____6508  ->
                               match uu____6508 with
                               | (l,uu____6518) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6484 FStar_Util.must  in
                      (match uu____6474 with
                       | (uu____6564,op) ->
                           let uu____6576 = op arg_tms1  in
                           (uu____6576, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6587 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6587
       then
         let uu____6588 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6589 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6590 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6588 uu____6589
           uu____6590
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6596 ->
           let uu____6621 =
             let uu____6622 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6623 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6624 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6625 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6622
               uu____6623 uu____6624 uu____6625
              in
           failwith uu____6621
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6630 =
             let uu____6631 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6632 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6633 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6634 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6631
               uu____6632 uu____6633 uu____6634
              in
           failwith uu____6630
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6640 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____6640 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6642 =
             let uu____6643 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6643
              in
           failwith uu____6642
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____6650),uu____6651) ->
           let uu____6700 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____6708 -> false  in
           if uu____6700
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____6723) ->
           let tv =
             let uu____6729 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____6729
              in
           let t1 =
             let uu____6733 =
               let uu____6742 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____6742]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____6733
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6762) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6770 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6770, [])
       | FStar_Syntax_Syntax.Tm_type uu____6771 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6773) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6798 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6798 with
            | (binders1,res) ->
                let uu____6809 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6809
                then
                  let uu____6814 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6814 with
                   | (vars,guards,env',decls,uu____6839) ->
                       let fsym =
                         let uu____6857 = varops.fresh "f"  in
                         (uu____6857, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6860 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___114_6869 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___114_6869.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___114_6869.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___114_6869.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___114_6869.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___114_6869.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___114_6869.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___114_6869.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___114_6869.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___114_6869.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___114_6869.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___114_6869.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___114_6869.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___114_6869.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___114_6869.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___114_6869.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___114_6869.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___114_6869.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___114_6869.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___114_6869.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___114_6869.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___114_6869.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___114_6869.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___114_6869.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___114_6869.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___114_6869.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___114_6869.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___114_6869.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___114_6869.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___114_6869.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___114_6869.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___114_6869.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___114_6869.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___114_6869.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___114_6869.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___114_6869.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___114_6869.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___114_6869.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6860 with
                        | (pre_opt,res_t) ->
                            let uu____6880 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6880 with
                             | (res_pred,decls') ->
                                 let uu____6891 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6900 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6900, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6902 =
                                         encode_formula pre env'  in
                                       (match uu____6902 with
                                        | (guard,decls0) ->
                                            let uu____6913 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6913, decls0))
                                    in
                                 (match uu____6891 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6921 =
                                          let uu____6932 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6932)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6921
                                         in
                                      let cvars =
                                        let uu____6948 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6948
                                          (FStar_List.filter
                                             (fun uu____6974  ->
                                                match uu____6974 with
                                                | (x,uu____6980) ->
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
                                      let uu____6993 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6993 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____7001 =
                                             let uu____7002 =
                                               let uu____7009 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____7009)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7002
                                              in
                                           (uu____7001,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____7027 =
                                               let uu____7028 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____7028
                                                in
                                             varops.mk_unique uu____7027  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____7037 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____7037
                                             then
                                               let uu____7038 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7038
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
                                             let uu____7044 =
                                               let uu____7051 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____7051)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7044
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
                                             let uu____7063 =
                                               let uu____7070 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____7070,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7063
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
                                             let uu____7083 =
                                               let uu____7090 =
                                                 let uu____7091 =
                                                   let uu____7102 =
                                                     let uu____7103 =
                                                       let uu____7108 =
                                                         let uu____7109 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____7109
                                                          in
                                                       (f_has_t, uu____7108)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____7103
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____7102)
                                                    in
                                                 mkForall_fuel uu____7091  in
                                               (uu____7090,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7083
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____7124 =
                                               let uu____7131 =
                                                 let uu____7132 =
                                                   let uu____7143 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____7143)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____7132
                                                  in
                                               (uu____7131,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7124
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
                                           ((let uu____7160 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____7160);
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
                     let uu____7171 =
                       let uu____7178 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____7178,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7171  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____7188 =
                       let uu____7195 =
                         let uu____7196 =
                           let uu____7207 =
                             let uu____7208 =
                               let uu____7213 =
                                 let uu____7214 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____7214
                                  in
                               (f_has_t, uu____7213)  in
                             FStar_SMTEncoding_Util.mkImp uu____7208  in
                           ([[f_has_t]], [fsym], uu____7207)  in
                         mkForall_fuel uu____7196  in
                       (uu____7195, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7188  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____7231 ->
           let uu____7238 =
             let uu____7243 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____7243 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____7250;
                 FStar_Syntax_Syntax.vars = uu____7251;_} ->
                 let uu____7258 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____7258 with
                  | (b,f1) ->
                      let uu____7277 =
                        let uu____7278 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7278  in
                      (uu____7277, f1))
             | uu____7287 -> failwith "impossible"  in
           (match uu____7238 with
            | (x,f) ->
                let uu____7298 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7298 with
                 | (base_t,decls) ->
                     let uu____7309 = gen_term_var env x  in
                     (match uu____7309 with
                      | (x1,xtm,env') ->
                          let uu____7323 = encode_formula f env'  in
                          (match uu____7323 with
                           | (refinement,decls') ->
                               let uu____7334 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7334 with
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
                                      let uu____7354 =
                                        let uu____7361 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7368 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7361
                                          uu____7368
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7354
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7409  ->
                                              match uu____7409 with
                                              | (y,uu____7415) ->
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
                                    let uu____7442 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7442 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7450 =
                                           let uu____7451 =
                                             let uu____7458 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7458)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7451
                                            in
                                         (uu____7450,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7477 =
                                             let uu____7478 =
                                               let uu____7479 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7479
                                                in
                                             Prims.strcat module_name
                                               uu____7478
                                              in
                                           varops.mk_unique uu____7477  in
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
                                           let uu____7491 =
                                             let uu____7498 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7498)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7491
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
                                           let uu____7513 =
                                             let uu____7520 =
                                               let uu____7521 =
                                                 let uu____7532 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7532)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7521
                                                in
                                             (uu____7520,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7513
                                            in
                                         let t_kinding =
                                           let uu____7542 =
                                             let uu____7549 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7549,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7542
                                            in
                                         let t_interp =
                                           let uu____7559 =
                                             let uu____7566 =
                                               let uu____7567 =
                                                 let uu____7578 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7578)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7567
                                                in
                                             let uu____7595 =
                                               let uu____7596 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7596
                                                in
                                             (uu____7566, uu____7595,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7559
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7601 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7601);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar uv ->
           let ttm =
             let uu____7604 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7604  in
           let uu____7605 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____7605 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7617 =
                    let uu____7624 =
                      let uu____7625 =
                        let uu____7626 =
                          let uu____7627 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7627
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7626  in
                      varops.mk_unique uu____7625  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7624)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7617  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7628 ->
           let uu____7643 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7643 with
            | (head1,args_e) ->
                let uu____7678 =
                  let uu____7691 =
                    let uu____7692 = FStar_Syntax_Subst.compress head1  in
                    uu____7692.FStar_Syntax_Syntax.n  in
                  (uu____7691, args_e)  in
                (match uu____7678 with
                 | uu____7707 when head_redex env head1 ->
                     let uu____7720 = whnf env t  in
                     encode_term uu____7720 env
                 | uu____7721 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7740 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7754;
                       FStar_Syntax_Syntax.vars = uu____7755;_},uu____7756),uu____7757::
                    (v1,uu____7759)::(v2,uu____7761)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7812 = encode_term v1 env  in
                     (match uu____7812 with
                      | (v11,decls1) ->
                          let uu____7823 = encode_term v2 env  in
                          (match uu____7823 with
                           | (v21,decls2) ->
                               let uu____7834 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7834,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7836::(v1,uu____7838)::(v2,uu____7840)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7887 = encode_term v1 env  in
                     (match uu____7887 with
                      | (v11,decls1) ->
                          let uu____7898 = encode_term v2 env  in
                          (match uu____7898 with
                           | (v21,decls2) ->
                               let uu____7909 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7909,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7911)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7937)::(rng,uu____7939)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7974) ->
                     let e0 =
                       let uu____7992 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7992
                        in
                     ((let uu____8000 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____8000
                       then
                         let uu____8001 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____8001
                       else ());
                      (let e =
                         let uu____8006 =
                           let uu____8011 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____8012 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____8011
                             uu____8012
                            in
                         uu____8006 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____8021),(arg,uu____8023)::[]) -> encode_term arg env
                 | uu____8048 ->
                     let uu____8061 = encode_args args_e env  in
                     (match uu____8061 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____8118 = encode_term head1 env  in
                            match uu____8118 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____8182 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____8182 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8260  ->
                                                 fun uu____8261  ->
                                                   match (uu____8260,
                                                           uu____8261)
                                                   with
                                                   | ((bv,uu____8283),
                                                      (a,uu____8285)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8303 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8303
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8304 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8304 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8319 =
                                                   let uu____8326 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8335 =
                                                     let uu____8336 =
                                                       let uu____8337 =
                                                         let uu____8338 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8338
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8337
                                                        in
                                                     varops.mk_unique
                                                       uu____8336
                                                      in
                                                   (uu____8326,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8335)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8319
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8355 = lookup_free_var_sym env fv  in
                            match uu____8355 with
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
                                   FStar_Syntax_Syntax.pos = uu____8387;
                                   FStar_Syntax_Syntax.vars = uu____8388;_},uu____8389)
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
                                   FStar_Syntax_Syntax.pos = uu____8400;
                                   FStar_Syntax_Syntax.vars = uu____8401;_},uu____8402)
                                ->
                                let uu____8407 =
                                  let uu____8408 =
                                    let uu____8413 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8413
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8408
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8407
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8443 =
                                  let uu____8444 =
                                    let uu____8449 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8449
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8444
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8443
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8478,(FStar_Util.Inl t1,uu____8480),uu____8481)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8530,(FStar_Util.Inr c,uu____8532),uu____8533)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8582 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8609 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8609
                                  in
                               let uu____8610 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8610 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8626;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8627;_},uu____8628)
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
                                     | uu____8642 ->
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
           let uu____8707 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8707 with
            | (bs1,body1,opening) ->
                let fallback uu____8732 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8737 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8737, [decl])  in
                let is_impure rc =
                  let uu____8746 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8746 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8758 =
                          let uu____8771 =
                            FStar_TypeChecker_Env.get_range env.tcenv  in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8771 env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8758 with
                         | (t1,uu____8773,uu____8774) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8792 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8792
                  then
                    let uu____8795 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8795
                  else
                    (let uu____8797 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8797
                     then
                       let uu____8800 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8800
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8807 =
                         let uu____8812 =
                           let uu____8813 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8813
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8812)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8807);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8815 =
                       (is_impure rc) &&
                         (let uu____8817 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8817)
                        in
                     if uu____8815
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8824 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8824 with
                        | (vars,guards,envbody,decls,uu____8849) ->
                            let body2 =
                              let uu____8863 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8863
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8865 = encode_term body2 envbody  in
                            (match uu____8865 with
                             | (body3,decls') ->
                                 let uu____8876 =
                                   let uu____8883 = codomain_eff rc  in
                                   match uu____8883 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8898 = encode_term tfun env
                                          in
                                       (match uu____8898 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8876 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8924 =
                                          let uu____8935 =
                                            let uu____8936 =
                                              let uu____8941 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8941, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8936
                                             in
                                          ([], vars, uu____8935)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8924
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
                                            let uu____8955 =
                                              let uu____8962 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8962
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8955
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8985 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8985 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8993 =
                                             let uu____8994 =
                                               let uu____9001 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____9001)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8994
                                              in
                                           (uu____8993,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____9010 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____9010 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____9019 =
                                                    let uu____9020 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____9020 = cache_size
                                                     in
                                                  if uu____9019
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
                                                    let uu____9032 =
                                                      let uu____9033 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____9033
                                                       in
                                                    varops.mk_unique
                                                      uu____9032
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
                                                  let uu____9038 =
                                                    let uu____9045 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____9045)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____9038
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
                                                      let uu____9063 =
                                                        let uu____9064 =
                                                          let uu____9071 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____9071,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____9064
                                                         in
                                                      [uu____9063]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____9082 =
                                                    let uu____9089 =
                                                      let uu____9090 =
                                                        let uu____9101 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____9101)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____9090
                                                       in
                                                    (uu____9089,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____9082
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
                                                ((let uu____9114 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____9114);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____9115,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____9116;
                          FStar_Syntax_Syntax.lbunivs = uu____9117;
                          FStar_Syntax_Syntax.lbtyp = uu____9118;
                          FStar_Syntax_Syntax.lbeff = uu____9119;
                          FStar_Syntax_Syntax.lbdef = uu____9120;
                          FStar_Syntax_Syntax.lbattrs = uu____9121;
                          FStar_Syntax_Syntax.lbpos = uu____9122;_}::uu____9123),uu____9124)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____9154;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____9156;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____9158;
                FStar_Syntax_Syntax.lbpos = uu____9159;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____9183 ->
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
              let uu____9253 =
                let uu____9258 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9258 env  in
              match uu____9253 with
              | (ee1,decls1) ->
                  let uu____9283 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9283 with
                   | (xs,e21) ->
                       let uu____9302 = FStar_List.hd xs  in
                       (match uu____9302 with
                        | (x1,uu____9316) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9318 = encode_body e21 env'  in
                            (match uu____9318 with
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
            let uu____9348 =
              let uu____9355 =
                let uu____9356 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9356  in
              gen_term_var env uu____9355  in
            match uu____9348 with
            | (scrsym,scr',env1) ->
                let uu____9364 = encode_term e env1  in
                (match uu____9364 with
                 | (scr,decls) ->
                     let uu____9375 =
                       let encode_branch b uu____9404 =
                         match uu____9404 with
                         | (else_case,decls1) ->
                             let uu____9423 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9423 with
                              | (p,w,br) ->
                                  let uu____9449 = encode_pat env1 p  in
                                  (match uu____9449 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9486  ->
                                                   match uu____9486 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9493 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9509 =
                                               encode_term w1 env2  in
                                             (match uu____9509 with
                                              | (w2,decls2) ->
                                                  let uu____9520 =
                                                    let uu____9521 =
                                                      let uu____9526 =
                                                        let uu____9527 =
                                                          let uu____9532 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9532)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9527
                                                         in
                                                      (guard, uu____9526)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9521
                                                     in
                                                  (uu____9520, decls2))
                                          in
                                       (match uu____9493 with
                                        | (guard1,decls2) ->
                                            let uu____9541 =
                                              encode_br br env2  in
                                            (match uu____9541 with
                                             | (br1,decls3) ->
                                                 let uu____9554 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9554,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9375 with
                      | (match_tm,decls1) ->
                          let uu____9575 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9575, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____9597 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9597
       then
         let uu____9598 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9598
       else ());
      (let uu____9600 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9600 with
       | (vars,pat_term) ->
           let uu____9617 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9670  ->
                     fun v1  ->
                       match uu____9670 with
                       | (env1,vars1) ->
                           let uu____9722 = gen_term_var env1 v1  in
                           (match uu____9722 with
                            | (xx,uu____9744,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9617 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9827 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9828 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9829 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9837 = encode_const c env1  in
                      (match uu____9837 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9851::uu____9852 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9855 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9878 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9878 with
                        | (uu____9885,uu____9886::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9889 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9922  ->
                                  match uu____9922 with
                                  | (arg,uu____9930) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9936 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9936))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9967) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9998 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____10021 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____10065  ->
                                  match uu____10065 with
                                  | (arg,uu____10079) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____10085 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____10085))
                         in
                      FStar_All.pipe_right uu____10021 FStar_List.flatten
                   in
                let pat_term1 uu____10115 = encode_term pat_term env1  in
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
      let uu____10125 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10169  ->
                fun uu____10170  ->
                  match (uu____10169, uu____10170) with
                  | ((tms,decls),(t,uu____10206)) ->
                      let uu____10227 = encode_term t env  in
                      (match uu____10227 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10125 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10284 = FStar_Syntax_Util.list_elements e  in
        match uu____10284 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____10307 =
          let uu____10320 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10320 FStar_Syntax_Util.head_and_args
           in
        match uu____10307 with
        | (head1,args) ->
            let uu____10353 =
              let uu____10366 =
                let uu____10367 = FStar_Syntax_Util.un_uinst head1  in
                uu____10367.FStar_Syntax_Syntax.n  in
              (uu____10366, args)  in
            (match uu____10353 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10381,uu____10382)::(e,uu____10384)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10419 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____10459 =
            let uu____10472 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10472 FStar_Syntax_Util.head_and_args
             in
          match uu____10459 with
          | (head1,args) ->
              let uu____10507 =
                let uu____10520 =
                  let uu____10521 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10521.FStar_Syntax_Syntax.n  in
                (uu____10520, args)  in
              (match uu____10507 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10538)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10565 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10587 = smt_pat_or t1  in
            (match uu____10587 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10603 = list_elements1 e  in
                 FStar_All.pipe_right uu____10603
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10621 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10621
                           (FStar_List.map one_pat)))
             | uu____10632 ->
                 let uu____10637 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10637])
        | uu____10658 ->
            let uu____10661 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10661]
         in
      let uu____10682 =
        let uu____10701 =
          let uu____10702 = FStar_Syntax_Subst.compress t  in
          uu____10702.FStar_Syntax_Syntax.n  in
        match uu____10701 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10741 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10741 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10784;
                        FStar_Syntax_Syntax.effect_name = uu____10785;
                        FStar_Syntax_Syntax.result_typ = uu____10786;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10788)::(post,uu____10790)::(pats,uu____10792)::[];
                        FStar_Syntax_Syntax.flags = uu____10793;_}
                      ->
                      let uu____10834 = lemma_pats pats  in
                      (binders1, pre, post, uu____10834)
                  | uu____10851 -> failwith "impos"))
        | uu____10870 -> failwith "Impos"  in
      match uu____10682 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___115_10918 = env  in
            {
              bindings = (uu___115_10918.bindings);
              depth = (uu___115_10918.depth);
              tcenv = (uu___115_10918.tcenv);
              warn = (uu___115_10918.warn);
              cache = (uu___115_10918.cache);
              nolabels = (uu___115_10918.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___115_10918.encode_non_total_function_typ);
              current_module_name = (uu___115_10918.current_module_name)
            }  in
          let uu____10919 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10919 with
           | (vars,guards,env2,decls,uu____10944) ->
               let uu____10957 =
                 let uu____10972 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____11026 =
                             let uu____11037 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____11037
                               FStar_List.unzip
                              in
                           match uu____11026 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10972 FStar_List.unzip  in
               (match uu____10957 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___116_11189 = env2  in
                      {
                        bindings = (uu___116_11189.bindings);
                        depth = (uu___116_11189.depth);
                        tcenv = (uu___116_11189.tcenv);
                        warn = (uu___116_11189.warn);
                        cache = (uu___116_11189.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___116_11189.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___116_11189.encode_non_total_function_typ);
                        current_module_name =
                          (uu___116_11189.current_module_name)
                      }  in
                    let uu____11190 =
                      let uu____11195 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____11195 env3  in
                    (match uu____11190 with
                     | (pre1,decls'') ->
                         let uu____11202 =
                           let uu____11207 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____11207 env3  in
                         (match uu____11202 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____11217 =
                                let uu____11218 =
                                  let uu____11229 =
                                    let uu____11230 =
                                      let uu____11235 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____11235, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____11230
                                     in
                                  (pats, vars, uu____11229)  in
                                FStar_SMTEncoding_Util.mkForall uu____11218
                                 in
                              (uu____11217, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11244 = FStar_Syntax_Util.head_and_args t  in
      match uu____11244 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11297::(x,uu____11299)::(t1,uu____11301)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11348 = encode_term x env  in
               (match uu____11348 with
                | (x1,decls) ->
                    let uu____11361 = encode_term t1 env  in
                    (match uu____11361 with
                     | (t2,decls') ->
                         let uu____11374 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11374, (FStar_List.append decls decls'))))
           | uu____11377 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11402 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11402
        then
          let uu____11403 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11404 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11403 uu____11404
        else ()  in
      let enc f r l =
        let uu____11443 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11471 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11471 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11443 with
        | (decls,args) ->
            let uu____11500 =
              let uu___117_11501 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11501.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11501.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11500, decls)
         in
      let const_op f r uu____11526 =
        let uu____11529 = f r  in (uu____11529, [])  in
      let un_op f l =
        let uu____11552 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11552  in
      let bin_op f uu___93_11572 =
        match uu___93_11572 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11583 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11623 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11646  ->
                 match uu____11646 with
                 | (t,uu____11660) ->
                     let uu____11661 = encode_formula t env  in
                     (match uu____11661 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11623 with
        | (decls,phis) ->
            let uu____11690 =
              let uu___118_11691 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___118_11691.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___118_11691.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11690, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11754  ->
               match uu____11754 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11773) -> false
                    | uu____11774 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11789 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11789
        else
          (let uu____11803 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11803 r rf)
         in
      let mk_imp1 r uu___94_11838 =
        match uu___94_11838 with
        | (lhs,uu____11844)::(rhs,uu____11846)::[] ->
            let uu____11873 = encode_formula rhs env  in
            (match uu____11873 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11888) ->
                      (l1, decls1)
                  | uu____11893 ->
                      let uu____11894 = encode_formula lhs env  in
                      (match uu____11894 with
                       | (l2,decls2) ->
                           let uu____11905 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11905, (FStar_List.append decls1 decls2)))))
        | uu____11906 -> failwith "impossible"  in
      let mk_ite r uu___95_11933 =
        match uu___95_11933 with
        | (guard,uu____11939)::(_then,uu____11941)::(_else,uu____11943)::[]
            ->
            let uu____11980 = encode_formula guard env  in
            (match uu____11980 with
             | (g,decls1) ->
                 let uu____11991 = encode_formula _then env  in
                 (match uu____11991 with
                  | (t,decls2) ->
                      let uu____12002 = encode_formula _else env  in
                      (match uu____12002 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____12014 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____12043 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____12043  in
      let connectives =
        let uu____12063 =
          let uu____12078 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____12078)  in
        let uu____12101 =
          let uu____12118 =
            let uu____12133 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____12133)  in
          let uu____12156 =
            let uu____12173 =
              let uu____12190 =
                let uu____12205 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12205)  in
              let uu____12228 =
                let uu____12245 =
                  let uu____12262 =
                    let uu____12277 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12277)  in
                  [uu____12262;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12245  in
              uu____12190 :: uu____12228  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____12173  in
          uu____12118 :: uu____12156  in
        uu____12063 :: uu____12101  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12540 = encode_formula phi' env  in
            (match uu____12540 with
             | (phi2,decls) ->
                 let uu____12551 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12551, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12552 ->
            let uu____12559 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12559 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12598 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12598 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12610;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12612;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12614;
                 FStar_Syntax_Syntax.lbpos = uu____12615;_}::[]),e2)
            ->
            let uu____12639 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12639 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12686::(x,uu____12688)::(t,uu____12690)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12737 = encode_term x env  in
                 (match uu____12737 with
                  | (x1,decls) ->
                      let uu____12748 = encode_term t env  in
                      (match uu____12748 with
                       | (t1,decls') ->
                           let uu____12759 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12759, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12764)::(msg,uu____12766)::(phi2,uu____12768)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12813 =
                   let uu____12818 =
                     let uu____12819 = FStar_Syntax_Subst.compress r  in
                     uu____12819.FStar_Syntax_Syntax.n  in
                   let uu____12822 =
                     let uu____12823 = FStar_Syntax_Subst.compress msg  in
                     uu____12823.FStar_Syntax_Syntax.n  in
                   (uu____12818, uu____12822)  in
                 (match uu____12813 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12832))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12838 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12845)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12870 when head_redex env head2 ->
                 let uu____12883 = whnf env phi1  in
                 encode_formula uu____12883 env
             | uu____12884 ->
                 let uu____12897 = encode_term phi1 env  in
                 (match uu____12897 with
                  | (tt,decls) ->
                      let uu____12908 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___119_12911 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___119_12911.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___119_12911.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12908, decls)))
        | uu____12912 ->
            let uu____12913 = encode_term phi1 env  in
            (match uu____12913 with
             | (tt,decls) ->
                 let uu____12924 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___120_12927 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___120_12927.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___120_12927.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12924, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12971 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12971 with
        | (vars,guards,env2,decls,uu____13010) ->
            let uu____13023 =
              let uu____13036 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____13096 =
                          let uu____13107 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____13147  ->
                                    match uu____13147 with
                                    | (t,uu____13161) ->
                                        encode_smt_pattern t
                                          (let uu___121_13167 = env2  in
                                           {
                                             bindings =
                                               (uu___121_13167.bindings);
                                             depth = (uu___121_13167.depth);
                                             tcenv = (uu___121_13167.tcenv);
                                             warn = (uu___121_13167.warn);
                                             cache = (uu___121_13167.cache);
                                             nolabels =
                                               (uu___121_13167.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___121_13167.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___121_13167.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____13107 FStar_List.unzip
                           in
                        match uu____13096 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____13036 FStar_List.unzip  in
            (match uu____13023 with
             | (pats,decls') ->
                 let uu____13276 = encode_formula body env2  in
                 (match uu____13276 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13308;
                             FStar_SMTEncoding_Term.rng = uu____13309;_}::[])::[]
                            when
                            let uu____13324 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13324 = gf -> []
                        | uu____13325 -> guards  in
                      let uu____13330 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13330, body1,
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
                (fun uu____13394  ->
                   match uu____13394 with
                   | (x,uu____13400) ->
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
               let uu____13408 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13420 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____13420) uu____13408 tl1
                in
             let uu____13423 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13450  ->
                       match uu____13450 with
                       | (b,uu____13456) ->
                           let uu____13457 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____13457))
                in
             (match uu____13423 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13463) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____13477 =
                    let uu____13482 =
                      let uu____13483 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13483
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13482)
                     in
                  FStar_Errors.log_issue pos uu____13477)
          in
       let uu____13484 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13484 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13493 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13559  ->
                     match uu____13559 with
                     | (l,uu____13573) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13493 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13612,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13666 = encode_q_body env vars pats body  in
             match uu____13666 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13711 =
                     let uu____13722 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13722)  in
                   FStar_SMTEncoding_Term.mkForall uu____13711
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13745 = encode_q_body env vars pats body  in
             match uu____13745 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13789 =
                   let uu____13790 =
                     let uu____13801 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13801)  in
                   FStar_SMTEncoding_Term.mkExists uu____13790
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13789, decls))))

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
  let uu____13924 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13924 with
  | (asym,a) ->
      let uu____13931 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13931 with
       | (xsym,x) ->
           let uu____13938 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13938 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13992 =
                      let uu____14003 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____14003, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13992  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____14025 =
                      let uu____14032 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____14032)  in
                    FStar_SMTEncoding_Util.mkApp uu____14025  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____14045 =
                    let uu____14048 =
                      let uu____14051 =
                        let uu____14054 =
                          let uu____14055 =
                            let uu____14062 =
                              let uu____14063 =
                                let uu____14074 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____14074)  in
                              FStar_SMTEncoding_Util.mkForall uu____14063  in
                            (uu____14062, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____14055  in
                        let uu____14083 =
                          let uu____14086 =
                            let uu____14087 =
                              let uu____14094 =
                                let uu____14095 =
                                  let uu____14106 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____14106)  in
                                FStar_SMTEncoding_Util.mkForall uu____14095
                                 in
                              (uu____14094,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____14087  in
                          [uu____14086]  in
                        uu____14054 :: uu____14083  in
                      xtok_decl :: uu____14051  in
                    xname_decl :: uu____14048  in
                  (xtok1, (FStar_List.length vars), uu____14045)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____14196 =
                    let uu____14212 =
                      let uu____14225 =
                        let uu____14226 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____14226
                         in
                      quant axy uu____14225  in
                    (FStar_Parser_Const.op_Eq, uu____14212)  in
                  let uu____14238 =
                    let uu____14256 =
                      let uu____14272 =
                        let uu____14285 =
                          let uu____14286 =
                            let uu____14287 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14287  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14286
                           in
                        quant axy uu____14285  in
                      (FStar_Parser_Const.op_notEq, uu____14272)  in
                    let uu____14299 =
                      let uu____14317 =
                        let uu____14333 =
                          let uu____14346 =
                            let uu____14347 =
                              let uu____14348 =
                                let uu____14353 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14354 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14353, uu____14354)  in
                              FStar_SMTEncoding_Util.mkLT uu____14348  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14347
                             in
                          quant xy uu____14346  in
                        (FStar_Parser_Const.op_LT, uu____14333)  in
                      let uu____14366 =
                        let uu____14384 =
                          let uu____14400 =
                            let uu____14413 =
                              let uu____14414 =
                                let uu____14415 =
                                  let uu____14420 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14421 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14420, uu____14421)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14415  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14414
                               in
                            quant xy uu____14413  in
                          (FStar_Parser_Const.op_LTE, uu____14400)  in
                        let uu____14433 =
                          let uu____14451 =
                            let uu____14467 =
                              let uu____14480 =
                                let uu____14481 =
                                  let uu____14482 =
                                    let uu____14487 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14488 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14487, uu____14488)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14482  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14481
                                 in
                              quant xy uu____14480  in
                            (FStar_Parser_Const.op_GT, uu____14467)  in
                          let uu____14500 =
                            let uu____14518 =
                              let uu____14534 =
                                let uu____14547 =
                                  let uu____14548 =
                                    let uu____14549 =
                                      let uu____14554 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14555 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14554, uu____14555)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14549
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14548
                                   in
                                quant xy uu____14547  in
                              (FStar_Parser_Const.op_GTE, uu____14534)  in
                            let uu____14567 =
                              let uu____14585 =
                                let uu____14601 =
                                  let uu____14614 =
                                    let uu____14615 =
                                      let uu____14616 =
                                        let uu____14621 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14622 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14621, uu____14622)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14616
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14615
                                     in
                                  quant xy uu____14614  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14601)
                                 in
                              let uu____14634 =
                                let uu____14652 =
                                  let uu____14668 =
                                    let uu____14681 =
                                      let uu____14682 =
                                        let uu____14683 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14683
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14682
                                       in
                                    quant qx uu____14681  in
                                  (FStar_Parser_Const.op_Minus, uu____14668)
                                   in
                                let uu____14695 =
                                  let uu____14713 =
                                    let uu____14729 =
                                      let uu____14742 =
                                        let uu____14743 =
                                          let uu____14744 =
                                            let uu____14749 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14750 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14749, uu____14750)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14744
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14743
                                         in
                                      quant xy uu____14742  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14729)
                                     in
                                  let uu____14762 =
                                    let uu____14780 =
                                      let uu____14796 =
                                        let uu____14809 =
                                          let uu____14810 =
                                            let uu____14811 =
                                              let uu____14816 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14817 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14816, uu____14817)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14811
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14810
                                           in
                                        quant xy uu____14809  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14796)
                                       in
                                    let uu____14829 =
                                      let uu____14847 =
                                        let uu____14863 =
                                          let uu____14876 =
                                            let uu____14877 =
                                              let uu____14878 =
                                                let uu____14883 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14884 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14883, uu____14884)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14878
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14877
                                             in
                                          quant xy uu____14876  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14863)
                                         in
                                      let uu____14896 =
                                        let uu____14914 =
                                          let uu____14930 =
                                            let uu____14943 =
                                              let uu____14944 =
                                                let uu____14945 =
                                                  let uu____14950 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14951 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14950, uu____14951)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14945
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14944
                                               in
                                            quant xy uu____14943  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14930)
                                           in
                                        let uu____14963 =
                                          let uu____14981 =
                                            let uu____14997 =
                                              let uu____15010 =
                                                let uu____15011 =
                                                  let uu____15012 =
                                                    let uu____15017 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____15018 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____15017,
                                                      uu____15018)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15012
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____15011
                                                 in
                                              quant xy uu____15010  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14997)
                                             in
                                          let uu____15030 =
                                            let uu____15048 =
                                              let uu____15064 =
                                                let uu____15077 =
                                                  let uu____15078 =
                                                    let uu____15079 =
                                                      let uu____15084 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____15085 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____15084,
                                                        uu____15085)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____15079
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____15078
                                                   in
                                                quant xy uu____15077  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____15064)
                                               in
                                            let uu____15097 =
                                              let uu____15115 =
                                                let uu____15131 =
                                                  let uu____15144 =
                                                    let uu____15145 =
                                                      let uu____15146 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____15146
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____15145
                                                     in
                                                  quant qx uu____15144  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____15131)
                                                 in
                                              [uu____15115]  in
                                            uu____15048 :: uu____15097  in
                                          uu____14981 :: uu____15030  in
                                        uu____14914 :: uu____14963  in
                                      uu____14847 :: uu____14896  in
                                    uu____14780 :: uu____14829  in
                                  uu____14713 :: uu____14762  in
                                uu____14652 :: uu____14695  in
                              uu____14585 :: uu____14634  in
                            uu____14518 :: uu____14567  in
                          uu____14451 :: uu____14500  in
                        uu____14384 :: uu____14433  in
                      uu____14317 :: uu____14366  in
                    uu____14256 :: uu____14299  in
                  uu____14196 :: uu____14238  in
                let mk1 l v1 =
                  let uu____15417 =
                    let uu____15428 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15498  ->
                              match uu____15498 with
                              | (l',uu____15514) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____15428
                      (FStar_Option.map
                         (fun uu____15590  ->
                            match uu____15590 with | (uu____15613,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____15417 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15704  ->
                          match uu____15704 with
                          | (l',uu____15720) -> FStar_Ident.lid_equals l l'))
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
        let uu____15770 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15770 with
        | (xxsym,xx) ->
            let uu____15777 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15777 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15787 =
                   let uu____15794 =
                     let uu____15795 =
                       let uu____15806 =
                         let uu____15807 =
                           let uu____15812 =
                             let uu____15813 =
                               let uu____15818 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15818)  in
                             FStar_SMTEncoding_Util.mkEq uu____15813  in
                           (xx_has_type, uu____15812)  in
                         FStar_SMTEncoding_Util.mkImp uu____15807  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15806)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15795  in
                   let uu____15837 =
                     let uu____15838 =
                       let uu____15839 =
                         let uu____15840 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15840  in
                       Prims.strcat module_name uu____15839  in
                     varops.mk_unique uu____15838  in
                   (uu____15794, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15837)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15787)
  
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
    let uu____15888 =
      let uu____15889 =
        let uu____15896 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15896, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15889  in
    let uu____15897 =
      let uu____15900 =
        let uu____15901 =
          let uu____15908 =
            let uu____15909 =
              let uu____15920 =
                let uu____15921 =
                  let uu____15926 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15926)  in
                FStar_SMTEncoding_Util.mkImp uu____15921  in
              ([[typing_pred]], [xx], uu____15920)  in
            mkForall_fuel uu____15909  in
          (uu____15908, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15901  in
      [uu____15900]  in
    uu____15888 :: uu____15897  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15966 =
      let uu____15967 =
        let uu____15974 =
          let uu____15975 =
            let uu____15986 =
              let uu____15991 =
                let uu____15994 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15994]  in
              [uu____15991]  in
            let uu____15999 =
              let uu____16000 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16000 tt  in
            (uu____15986, [bb], uu____15999)  in
          FStar_SMTEncoding_Util.mkForall uu____15975  in
        (uu____15974, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15967  in
    let uu____16013 =
      let uu____16016 =
        let uu____16017 =
          let uu____16024 =
            let uu____16025 =
              let uu____16036 =
                let uu____16037 =
                  let uu____16042 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____16042)  in
                FStar_SMTEncoding_Util.mkImp uu____16037  in
              ([[typing_pred]], [xx], uu____16036)  in
            mkForall_fuel uu____16025  in
          (uu____16024, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16017  in
      [uu____16016]  in
    uu____15966 :: uu____16013  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____16090 =
        let uu____16091 =
          let uu____16098 =
            let uu____16101 =
              let uu____16104 =
                let uu____16107 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____16108 =
                  let uu____16111 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____16111]  in
                uu____16107 :: uu____16108  in
              tt :: uu____16104  in
            tt :: uu____16101  in
          ("Prims.Precedes", uu____16098)  in
        FStar_SMTEncoding_Util.mkApp uu____16091  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16090  in
    let precedes_y_x =
      let uu____16115 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16115  in
    let uu____16118 =
      let uu____16119 =
        let uu____16126 =
          let uu____16127 =
            let uu____16138 =
              let uu____16143 =
                let uu____16146 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____16146]  in
              [uu____16143]  in
            let uu____16151 =
              let uu____16152 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16152 tt  in
            (uu____16138, [bb], uu____16151)  in
          FStar_SMTEncoding_Util.mkForall uu____16127  in
        (uu____16126, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16119  in
    let uu____16165 =
      let uu____16168 =
        let uu____16169 =
          let uu____16176 =
            let uu____16177 =
              let uu____16188 =
                let uu____16189 =
                  let uu____16194 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____16194)  in
                FStar_SMTEncoding_Util.mkImp uu____16189  in
              ([[typing_pred]], [xx], uu____16188)  in
            mkForall_fuel uu____16177  in
          (uu____16176, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16169  in
      let uu____16211 =
        let uu____16214 =
          let uu____16215 =
            let uu____16222 =
              let uu____16223 =
                let uu____16234 =
                  let uu____16235 =
                    let uu____16240 =
                      let uu____16241 =
                        let uu____16244 =
                          let uu____16247 =
                            let uu____16250 =
                              let uu____16251 =
                                let uu____16256 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____16257 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____16256, uu____16257)  in
                              FStar_SMTEncoding_Util.mkGT uu____16251  in
                            let uu____16258 =
                              let uu____16261 =
                                let uu____16262 =
                                  let uu____16267 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____16268 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____16267, uu____16268)  in
                                FStar_SMTEncoding_Util.mkGTE uu____16262  in
                              let uu____16269 =
                                let uu____16272 =
                                  let uu____16273 =
                                    let uu____16278 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____16279 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____16278, uu____16279)  in
                                  FStar_SMTEncoding_Util.mkLT uu____16273  in
                                [uu____16272]  in
                              uu____16261 :: uu____16269  in
                            uu____16250 :: uu____16258  in
                          typing_pred_y :: uu____16247  in
                        typing_pred :: uu____16244  in
                      FStar_SMTEncoding_Util.mk_and_l uu____16241  in
                    (uu____16240, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____16235  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____16234)
                 in
              mkForall_fuel uu____16223  in
            (uu____16222,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____16215  in
        [uu____16214]  in
      uu____16168 :: uu____16211  in
    uu____16118 :: uu____16165  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16323 =
      let uu____16324 =
        let uu____16331 =
          let uu____16332 =
            let uu____16343 =
              let uu____16348 =
                let uu____16351 = FStar_SMTEncoding_Term.boxString b  in
                [uu____16351]  in
              [uu____16348]  in
            let uu____16356 =
              let uu____16357 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16357 tt  in
            (uu____16343, [bb], uu____16356)  in
          FStar_SMTEncoding_Util.mkForall uu____16332  in
        (uu____16331, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16324  in
    let uu____16370 =
      let uu____16373 =
        let uu____16374 =
          let uu____16381 =
            let uu____16382 =
              let uu____16393 =
                let uu____16394 =
                  let uu____16399 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____16399)  in
                FStar_SMTEncoding_Util.mkImp uu____16394  in
              ([[typing_pred]], [xx], uu____16393)  in
            mkForall_fuel uu____16382  in
          (uu____16381, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16374  in
      [uu____16373]  in
    uu____16323 :: uu____16370  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____16454 =
      let uu____16455 =
        let uu____16462 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____16462, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16455  in
    [uu____16454]  in
  let mk_and_interp env conj uu____16478 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16503 =
      let uu____16504 =
        let uu____16511 =
          let uu____16512 =
            let uu____16523 =
              let uu____16524 =
                let uu____16529 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16529, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16524  in
            ([[l_and_a_b]], [aa; bb], uu____16523)  in
          FStar_SMTEncoding_Util.mkForall uu____16512  in
        (uu____16511, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16504  in
    [uu____16503]  in
  let mk_or_interp env disj uu____16565 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16590 =
      let uu____16591 =
        let uu____16598 =
          let uu____16599 =
            let uu____16610 =
              let uu____16611 =
                let uu____16616 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16616, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16611  in
            ([[l_or_a_b]], [aa; bb], uu____16610)  in
          FStar_SMTEncoding_Util.mkForall uu____16599  in
        (uu____16598, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16591  in
    [uu____16590]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16677 =
      let uu____16678 =
        let uu____16685 =
          let uu____16686 =
            let uu____16697 =
              let uu____16698 =
                let uu____16703 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16703, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16698  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16697)  in
          FStar_SMTEncoding_Util.mkForall uu____16686  in
        (uu____16685, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16678  in
    [uu____16677]  in
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
    let uu____16774 =
      let uu____16775 =
        let uu____16782 =
          let uu____16783 =
            let uu____16794 =
              let uu____16795 =
                let uu____16800 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16800, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16795  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16794)  in
          FStar_SMTEncoding_Util.mkForall uu____16783  in
        (uu____16782, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16775  in
    [uu____16774]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16869 =
      let uu____16870 =
        let uu____16877 =
          let uu____16878 =
            let uu____16889 =
              let uu____16890 =
                let uu____16895 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16895, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16890  in
            ([[l_imp_a_b]], [aa; bb], uu____16889)  in
          FStar_SMTEncoding_Util.mkForall uu____16878  in
        (uu____16877, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16870  in
    [uu____16869]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16956 =
      let uu____16957 =
        let uu____16964 =
          let uu____16965 =
            let uu____16976 =
              let uu____16977 =
                let uu____16982 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16982, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16977  in
            ([[l_iff_a_b]], [aa; bb], uu____16976)  in
          FStar_SMTEncoding_Util.mkForall uu____16965  in
        (uu____16964, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16957  in
    [uu____16956]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____17032 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____17032  in
    let uu____17035 =
      let uu____17036 =
        let uu____17043 =
          let uu____17044 =
            let uu____17055 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____17055)  in
          FStar_SMTEncoding_Util.mkForall uu____17044  in
        (uu____17043, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17036  in
    [uu____17035]  in
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
      let uu____17113 =
        let uu____17120 =
          let uu____17123 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17123]  in
        ("Valid", uu____17120)  in
      FStar_SMTEncoding_Util.mkApp uu____17113  in
    let uu____17126 =
      let uu____17127 =
        let uu____17134 =
          let uu____17135 =
            let uu____17146 =
              let uu____17147 =
                let uu____17152 =
                  let uu____17153 =
                    let uu____17164 =
                      let uu____17169 =
                        let uu____17172 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17172]  in
                      [uu____17169]  in
                    let uu____17177 =
                      let uu____17178 =
                        let uu____17183 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17183, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17178  in
                    (uu____17164, [xx1], uu____17177)  in
                  FStar_SMTEncoding_Util.mkForall uu____17153  in
                (uu____17152, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17147  in
            ([[l_forall_a_b]], [aa; bb], uu____17146)  in
          FStar_SMTEncoding_Util.mkForall uu____17135  in
        (uu____17134, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17127  in
    [uu____17126]  in
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
      let uu____17257 =
        let uu____17264 =
          let uu____17267 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17267]  in
        ("Valid", uu____17264)  in
      FStar_SMTEncoding_Util.mkApp uu____17257  in
    let uu____17270 =
      let uu____17271 =
        let uu____17278 =
          let uu____17279 =
            let uu____17290 =
              let uu____17291 =
                let uu____17296 =
                  let uu____17297 =
                    let uu____17308 =
                      let uu____17313 =
                        let uu____17316 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17316]  in
                      [uu____17313]  in
                    let uu____17321 =
                      let uu____17322 =
                        let uu____17327 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17327, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17322  in
                    (uu____17308, [xx1], uu____17321)  in
                  FStar_SMTEncoding_Util.mkExists uu____17297  in
                (uu____17296, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17291  in
            ([[l_exists_a_b]], [aa; bb], uu____17290)  in
          FStar_SMTEncoding_Util.mkForall uu____17279  in
        (uu____17278, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17271  in
    [uu____17270]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____17379 =
      let uu____17380 =
        let uu____17387 =
          let uu____17388 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____17388 range_ty  in
        let uu____17389 = varops.mk_unique "typing_range_const"  in
        (uu____17387, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____17389)
         in
      FStar_SMTEncoding_Util.mkAssume uu____17380  in
    [uu____17379]  in
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
        let uu____17427 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17427 x1 t  in
      let uu____17428 =
        let uu____17439 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____17439)  in
      FStar_SMTEncoding_Util.mkForall uu____17428  in
    let uu____17456 =
      let uu____17457 =
        let uu____17464 =
          let uu____17465 =
            let uu____17476 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____17476)  in
          FStar_SMTEncoding_Util.mkForall uu____17465  in
        (uu____17464,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17457  in
    [uu____17456]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17524 =
      let uu____17525 =
        let uu____17532 =
          let uu____17533 =
            let uu____17548 =
              let uu____17549 =
                let uu____17554 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17555 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17554, uu____17555)  in
              FStar_SMTEncoding_Util.mkAnd uu____17549  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17548)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17533  in
        (uu____17532,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17525  in
    [uu____17524]  in
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
          let uu____18083 =
            FStar_Util.find_opt
              (fun uu____18119  ->
                 match uu____18119 with
                 | (l,uu____18133) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____18083 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____18173,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____18230 = encode_function_type_as_formula t env  in
        match uu____18230 with
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
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
              let uu____18288 =
                ((let uu____18291 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____18291) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____18288
              then
                let arg_sorts =
                  let uu____18301 =
                    let uu____18302 = FStar_Syntax_Subst.compress t_norm  in
                    uu____18302.FStar_Syntax_Syntax.n  in
                  match uu____18301 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____18308) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____18338  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____18343 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____18345 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____18345 with
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
                (let uu____18374 = prims.is lid  in
                 if uu____18374
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____18382 = prims.mk lid vname  in
                   match uu____18382 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____18409 =
                      let uu____18422 = curried_arrow_formals_comp t_norm  in
                      match uu____18422 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____18444 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____18444
                            then
                              let uu____18447 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___122_18450 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___122_18450.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___122_18450.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___122_18450.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___122_18450.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___122_18450.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___122_18450.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___122_18450.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___122_18450.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___122_18450.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___122_18450.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___122_18450.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___122_18450.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___122_18450.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___122_18450.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___122_18450.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___122_18450.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___122_18450.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___122_18450.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___122_18450.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___122_18450.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___122_18450.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___122_18450.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___122_18450.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___122_18450.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___122_18450.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___122_18450.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___122_18450.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___122_18450.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___122_18450.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___122_18450.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___122_18450.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___122_18450.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___122_18450.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___122_18450.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___122_18450.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___122_18450.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___122_18450.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____18447
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____18464 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____18464)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____18409 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____18520 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____18520 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____18545 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___96_18595  ->
                                       match uu___96_18595 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____18599 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18599 with
                                            | (uu____18620,(xxsym,uu____18622))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____18640 =
                                                  let uu____18641 =
                                                    let uu____18648 =
                                                      let uu____18649 =
                                                        let uu____18660 =
                                                          let uu____18661 =
                                                            let uu____18666 =
                                                              let uu____18667
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____18667
                                                               in
                                                            (vapp,
                                                              uu____18666)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____18661
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18660)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18649
                                                       in
                                                    (uu____18648,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18641
                                                   in
                                                [uu____18640])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____18678 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18678 with
                                            | (uu____18699,(xxsym,uu____18701))
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
                                                let uu____18724 =
                                                  let uu____18725 =
                                                    let uu____18732 =
                                                      let uu____18733 =
                                                        let uu____18744 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18744)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18733
                                                       in
                                                    (uu____18732,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18725
                                                   in
                                                [uu____18724])
                                       | uu____18753 -> []))
                                in
                             let uu____18754 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____18754 with
                              | (vars,guards,env',decls1,uu____18781) ->
                                  let uu____18794 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18807 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18807, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18811 =
                                          encode_formula p env'  in
                                        (match uu____18811 with
                                         | (g,ds) ->
                                             let uu____18824 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____18824,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18794 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____18841 =
                                           let uu____18848 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____18848)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____18841
                                          in
                                       let uu____18853 =
                                         let vname_decl =
                                           let uu____18861 =
                                             let uu____18872 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____18888  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____18872,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____18861
                                            in
                                         let uu____18895 =
                                           let env2 =
                                             let uu___123_18901 = env1  in
                                             {
                                               bindings =
                                                 (uu___123_18901.bindings);
                                               depth = (uu___123_18901.depth);
                                               tcenv = (uu___123_18901.tcenv);
                                               warn = (uu___123_18901.warn);
                                               cache = (uu___123_18901.cache);
                                               nolabels =
                                                 (uu___123_18901.nolabels);
                                               use_zfuel_name =
                                                 (uu___123_18901.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___123_18901.current_module_name)
                                             }  in
                                           let uu____18902 =
                                             let uu____18903 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____18903
                                              in
                                           if uu____18902
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____18895 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____18918::uu____18919 ->
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
                                                     let uu____18959 =
                                                       let uu____18970 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____18970)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____18959
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____18989 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____18990 =
                                               match formals with
                                               | [] ->
                                                   let uu____19007 =
                                                     let uu____19008 =
                                                       let uu____19011 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____19011
                                                        in
                                                     replace_free_var env1
                                                       lid arity vname
                                                       uu____19008
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____19007)
                                               | uu____19020 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____19025 =
                                                       let uu____19032 =
                                                         let uu____19033 =
                                                           let uu____19044 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____19044)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____19033
                                                          in
                                                       (uu____19032,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____19025
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____18990 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____18853 with
                                        | (decls2,env2) ->
                                            let uu____19083 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____19091 =
                                                encode_term res_t1 env'  in
                                              match uu____19091 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____19104 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____19104, decls)
                                               in
                                            (match uu____19083 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____19115 =
                                                     let uu____19122 =
                                                       let uu____19123 =
                                                         let uu____19134 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____19134)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____19123
                                                        in
                                                     (uu____19122,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____19115
                                                    in
                                                 let freshness =
                                                   let uu____19146 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____19146
                                                   then
                                                     let uu____19151 =
                                                       let uu____19152 =
                                                         let uu____19163 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____19178 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____19163,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____19178)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____19152
                                                        in
                                                     let uu____19181 =
                                                       let uu____19184 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____19184]  in
                                                     uu____19151 ::
                                                       uu____19181
                                                   else []  in
                                                 let g =
                                                   let uu____19189 =
                                                     let uu____19192 =
                                                       let uu____19195 =
                                                         let uu____19198 =
                                                           let uu____19201 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____19201
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____19198
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____19195
                                                        in
                                                     FStar_List.append decls2
                                                       uu____19192
                                                      in
                                                   FStar_List.append decls11
                                                     uu____19189
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (fvar_binding,FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____19242 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19242 with
          | FStar_Pervasives_Native.None  ->
              let uu____19253 = encode_free_var false env x t t_norm []  in
              (match uu____19253 with
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
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
            let uu____19320 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____19320 with
            | (decls,env1) ->
                let uu____19339 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____19339
                then
                  let uu____19346 =
                    let uu____19349 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____19349  in
                  (uu____19346, env1)
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
             (fun uu____19407  ->
                fun lb  ->
                  match uu____19407 with
                  | (decls,env1) ->
                      let uu____19427 =
                        let uu____19434 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____19434
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____19427 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____19457 = FStar_Syntax_Util.head_and_args t  in
    match uu____19457 with
    | (hd1,args) ->
        let uu____19488 =
          let uu____19489 = FStar_Syntax_Util.un_uinst hd1  in
          uu____19489.FStar_Syntax_Syntax.n  in
        (match uu____19488 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____19493,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____19512 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____19540  ->
      fun quals  ->
        match uu____19540 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____19632 = FStar_Util.first_N nbinders formals  in
              match uu____19632 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19713  ->
                         fun uu____19714  ->
                           match (uu____19713, uu____19714) with
                           | ((formal,uu____19732),(binder,uu____19734)) ->
                               let uu____19743 =
                                 let uu____19750 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19750)  in
                               FStar_Syntax_Syntax.NT uu____19743) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19762 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19793  ->
                              match uu____19793 with
                              | (x,i) ->
                                  let uu____19804 =
                                    let uu___124_19805 = x  in
                                    let uu____19806 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___124_19805.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___124_19805.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19806
                                    }  in
                                  (uu____19804, i)))
                       in
                    FStar_All.pipe_right uu____19762
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19824 =
                      let uu____19829 = FStar_Syntax_Subst.compress body  in
                      let uu____19830 =
                        let uu____19831 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____19831
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____19829
                        uu____19830
                       in
                    uu____19824 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____19910 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____19910
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___125_19915 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___125_19915.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___125_19915.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___125_19915.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___125_19915.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___125_19915.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___125_19915.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___125_19915.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___125_19915.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___125_19915.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___125_19915.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___125_19915.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___125_19915.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___125_19915.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___125_19915.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___125_19915.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___125_19915.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___125_19915.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___125_19915.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___125_19915.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___125_19915.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___125_19915.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___125_19915.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___125_19915.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___125_19915.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___125_19915.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___125_19915.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___125_19915.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___125_19915.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___125_19915.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___125_19915.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___125_19915.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___125_19915.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___125_19915.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___125_19915.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___125_19915.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___125_19915.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___125_19915.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____19956 = FStar_Syntax_Util.abs_formals e  in
                match uu____19956 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____20028::uu____20029 ->
                         let uu____20044 =
                           let uu____20045 =
                             let uu____20048 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____20048
                              in
                           uu____20045.FStar_Syntax_Syntax.n  in
                         (match uu____20044 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____20097 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____20097 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____20145 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____20145
                                   then
                                     let uu____20184 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____20184 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____20282  ->
                                                   fun uu____20283  ->
                                                     match (uu____20282,
                                                             uu____20283)
                                                     with
                                                     | ((x,uu____20301),
                                                        (b,uu____20303)) ->
                                                         let uu____20312 =
                                                           let uu____20319 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____20319)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____20312)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____20327 =
                                            let uu____20352 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____20352)
                                             in
                                          (uu____20327, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____20434 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____20434 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____20535) ->
                              let uu____20540 =
                                let uu____20565 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____20565  in
                              (uu____20540, true)
                          | uu____20642 when Prims.op_Negation norm1 ->
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
                          | uu____20644 ->
                              let uu____20645 =
                                let uu____20646 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____20647 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____20646
                                  uu____20647
                                 in
                              failwith uu____20645)
                     | uu____20676 ->
                         let rec aux' t_norm2 =
                           let uu____20709 =
                             let uu____20710 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____20710.FStar_Syntax_Syntax.n  in
                           match uu____20709 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____20757 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____20757 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____20793 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____20793 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20883)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20888 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20948 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20948
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20960 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____21023  ->
                            fun lb  ->
                              match uu____21023 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____21078 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____21078
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____21081 =
                                      let uu____21090 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____21090
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____21081 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____20960 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____21215 =
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
                        | uu____21221 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____21229 = mk_fv ()  in
                                   mk_Apply uu____21229 vars)
                            else
                              (let uu____21231 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____21231)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____21291;
                             FStar_Syntax_Syntax.lbeff = uu____21292;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____21294;
                             FStar_Syntax_Syntax.lbpos = uu____21295;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____21319 =
                              let uu____21326 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____21326 with
                              | (tcenv',uu____21342,e_t) ->
                                  let uu____21348 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____21359 -> failwith "Impossible"
                                     in
                                  (match uu____21348 with
                                   | (e1,t_norm1) ->
                                       ((let uu___128_21375 = env2  in
                                         {
                                           bindings =
                                             (uu___128_21375.bindings);
                                           depth = (uu___128_21375.depth);
                                           tcenv = tcenv';
                                           warn = (uu___128_21375.warn);
                                           cache = (uu___128_21375.cache);
                                           nolabels =
                                             (uu___128_21375.nolabels);
                                           use_zfuel_name =
                                             (uu___128_21375.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___128_21375.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___128_21375.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____21319 with
                             | (env',e1,t_norm1) ->
                                 let uu____21385 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____21385 with
                                  | ((binders,body,uu____21406,t_body),curry)
                                      ->
                                      ((let uu____21418 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____21418
                                        then
                                          let uu____21419 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____21420 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____21419 uu____21420
                                        else ());
                                       (let uu____21422 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____21422 with
                                        | (vars,guards,env'1,binder_decls,uu____21449)
                                            ->
                                            let body1 =
                                              let uu____21463 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____21463
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
                                              let uu____21484 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____21484 curry fvb
                                                vars
                                               in
                                            let uu____21485 =
                                              let uu____21494 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____21494
                                              then
                                                let uu____21505 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____21506 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____21505, uu____21506)
                                              else
                                                (let uu____21516 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____21516))
                                               in
                                            (match uu____21485 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____21539 =
                                                     let uu____21546 =
                                                       let uu____21547 =
                                                         let uu____21558 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____21558)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____21547
                                                        in
                                                     let uu____21567 =
                                                       let uu____21568 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21568
                                                        in
                                                     (uu____21546,
                                                       uu____21567,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____21539
                                                    in
                                                 let uu____21569 =
                                                   let uu____21572 =
                                                     let uu____21575 =
                                                       let uu____21578 =
                                                         let uu____21581 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____21581
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____21578
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____21575
                                                      in
                                                   FStar_List.append decls1
                                                     uu____21572
                                                    in
                                                 (uu____21569, env2))))))
                        | uu____21586 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____21649 = varops.fresh "fuel"  in
                          (uu____21649, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21652 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____21699  ->
                                  fun fvb  ->
                                    match uu____21699 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____21745 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21745  in
                                        let gtok =
                                          let uu____21747 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21747  in
                                        let env4 =
                                          let uu____21749 =
                                            let uu____21752 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____21752
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____21749
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____21652 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21858 t_norm
                              uu____21860 =
                              match (uu____21858, uu____21860) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____21888;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____21889;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____21891;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____21892;_})
                                  ->
                                  let uu____21913 =
                                    let uu____21920 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21920 with
                                    | (tcenv',uu____21936,e_t) ->
                                        let uu____21942 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21953 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21942 with
                                         | (e1,t_norm1) ->
                                             ((let uu___129_21969 = env3  in
                                               {
                                                 bindings =
                                                   (uu___129_21969.bindings);
                                                 depth =
                                                   (uu___129_21969.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___129_21969.warn);
                                                 cache =
                                                   (uu___129_21969.cache);
                                                 nolabels =
                                                   (uu___129_21969.nolabels);
                                                 use_zfuel_name =
                                                   (uu___129_21969.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___129_21969.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___129_21969.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21913 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21984 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21984
                                         then
                                           let uu____21985 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21986 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21987 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21985 uu____21986
                                             uu____21987
                                         else ());
                                        (let uu____21989 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____21989 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____22026 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____22026
                                               then
                                                 let uu____22027 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____22028 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____22029 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____22030 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____22027 uu____22028
                                                   uu____22029 uu____22030
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____22034 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____22034 with
                                               | (vars,guards,env'1,binder_decls,uu____22065)
                                                   ->
                                                   let decl_g =
                                                     let uu____22079 =
                                                       let uu____22090 =
                                                         let uu____22093 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____22093
                                                          in
                                                       (g, uu____22090,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____22079
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
                                                     let uu____22106 =
                                                       let uu____22113 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____22113)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22106
                                                      in
                                                   let gsapp =
                                                     let uu____22119 =
                                                       let uu____22126 =
                                                         let uu____22129 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____22129 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22126)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22119
                                                      in
                                                   let gmax =
                                                     let uu____22135 =
                                                       let uu____22142 =
                                                         let uu____22145 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____22145 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22142)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22135
                                                      in
                                                   let body1 =
                                                     let uu____22151 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____22151
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____22153 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____22153 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____22171 =
                                                            let uu____22178 =
                                                              let uu____22179
                                                                =
                                                                let uu____22194
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
                                                                  uu____22194)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____22179
                                                               in
                                                            let uu____22205 =
                                                              let uu____22206
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____22206
                                                               in
                                                            (uu____22178,
                                                              uu____22205,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22171
                                                           in
                                                        let eqn_f =
                                                          let uu____22208 =
                                                            let uu____22215 =
                                                              let uu____22216
                                                                =
                                                                let uu____22227
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____22227)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22216
                                                               in
                                                            (uu____22215,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22208
                                                           in
                                                        let eqn_g' =
                                                          let uu____22237 =
                                                            let uu____22244 =
                                                              let uu____22245
                                                                =
                                                                let uu____22256
                                                                  =
                                                                  let uu____22257
                                                                    =
                                                                    let uu____22262
                                                                    =
                                                                    let uu____22263
                                                                    =
                                                                    let uu____22270
                                                                    =
                                                                    let uu____22273
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____22273
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____22270)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____22263
                                                                     in
                                                                    (gsapp,
                                                                    uu____22262)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____22257
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____22256)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22245
                                                               in
                                                            (uu____22244,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22237
                                                           in
                                                        let uu____22284 =
                                                          let uu____22293 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____22293
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____22322)
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
                                                                  let uu____22343
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____22343
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____22344
                                                                  =
                                                                  let uu____22351
                                                                    =
                                                                    let uu____22352
                                                                    =
                                                                    let uu____22363
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22363)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22352
                                                                     in
                                                                  (uu____22351,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____22344
                                                                 in
                                                              let uu____22372
                                                                =
                                                                let uu____22379
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____22379
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____22392
                                                                    =
                                                                    let uu____22395
                                                                    =
                                                                    let uu____22396
                                                                    =
                                                                    let uu____22403
                                                                    =
                                                                    let uu____22404
                                                                    =
                                                                    let uu____22415
                                                                    =
                                                                    let uu____22416
                                                                    =
                                                                    let uu____22421
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____22421,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____22416
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22415)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22404
                                                                     in
                                                                    (uu____22403,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____22396
                                                                     in
                                                                    [uu____22395]
                                                                     in
                                                                    (d3,
                                                                    uu____22392)
                                                                 in
                                                              (match uu____22372
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
                                                        (match uu____22284
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
                            let uu____22474 =
                              let uu____22487 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22544  ->
                                   fun uu____22545  ->
                                     match (uu____22544, uu____22545) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22660 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22660 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22487
                               in
                            (match uu____22474 with
                             | (decls2,eqns,env01) ->
                                 let uu____22733 =
                                   let isDeclFun uu___97_22747 =
                                     match uu___97_22747 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22748 -> true
                                     | uu____22759 -> false  in
                                   let uu____22760 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22760
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22733 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22800 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___98_22804  ->
                                 match uu___98_22804 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22805 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22811 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22811)))
                         in
                      if uu____22800
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
                   let uu____22863 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22863
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
        let uu____22924 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22924 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22928 = encode_sigelt' env se  in
      match uu____22928 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22940 =
                  let uu____22941 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22941  in
                [uu____22940]
            | uu____22942 ->
                let uu____22943 =
                  let uu____22946 =
                    let uu____22947 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22947  in
                  uu____22946 :: g  in
                let uu____22948 =
                  let uu____22951 =
                    let uu____22952 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22952  in
                  [uu____22951]  in
                FStar_List.append uu____22943 uu____22948
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
        let uu____22965 =
          let uu____22966 = FStar_Syntax_Subst.compress t  in
          uu____22966.FStar_Syntax_Syntax.n  in
        match uu____22965 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22970)) -> s = "opaque_to_smt"
        | uu____22971 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22978 =
          let uu____22979 = FStar_Syntax_Subst.compress t  in
          uu____22979.FStar_Syntax_Syntax.n  in
        match uu____22978 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22983)) -> s = "uninterpreted_by_smt"
        | uu____22984 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22989 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____22994 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____23005 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____23006 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____23007 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____23020 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23022 =
            let uu____23023 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____23023 Prims.op_Negation  in
          if uu____23022
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____23049 ->
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
               let uu____23079 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____23079 with
               | (formals,uu____23097) ->
                   let arity = FStar_List.length formals  in
                   let uu____23115 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____23115 with
                    | (aname,atok,env2) ->
                        let uu____23135 =
                          let uu____23140 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____23140 env2  in
                        (match uu____23135 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____23152 =
                                 let uu____23153 =
                                   let uu____23164 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____23180  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____23164,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____23153
                                  in
                               [uu____23152;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____23189 =
                               let aux uu____23245 uu____23246 =
                                 match (uu____23245, uu____23246) with
                                 | ((bv,uu____23298),(env3,acc_sorts,acc)) ->
                                     let uu____23336 = gen_term_var env3 bv
                                        in
                                     (match uu____23336 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____23189 with
                              | (uu____23408,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____23431 =
                                      let uu____23438 =
                                        let uu____23439 =
                                          let uu____23450 =
                                            let uu____23451 =
                                              let uu____23456 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____23456)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23451
                                             in
                                          ([[app]], xs_sorts, uu____23450)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23439
                                         in
                                      (uu____23438,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23431
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23468 =
                                      let uu____23475 =
                                        let uu____23476 =
                                          let uu____23487 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23487)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23476
                                         in
                                      (uu____23475,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23468
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23498 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23498 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23524,uu____23525)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23526 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____23526 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23541,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23547 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___99_23551  ->
                      match uu___99_23551 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23552 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23557 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23558 -> false))
               in
            Prims.op_Negation uu____23547  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23565 =
               let uu____23572 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23572 env fv t quals  in
             match uu____23565 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23587 =
                   let uu____23588 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23588  in
                 (uu____23587, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23594 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23594 with
           | (uu____23603,f1) ->
               let uu____23605 = encode_formula f1 env  in
               (match uu____23605 with
                | (f2,decls) ->
                    let g =
                      let uu____23619 =
                        let uu____23620 =
                          let uu____23627 =
                            let uu____23628 =
                              let uu____23629 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23629
                               in
                            FStar_Pervasives_Native.Some uu____23628  in
                          let uu____23630 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23627, uu____23630)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23620  in
                      [uu____23619]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23632) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23644 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23666 =
                       let uu____23669 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23669.FStar_Syntax_Syntax.fv_name  in
                     uu____23666.FStar_Syntax_Syntax.v  in
                   let uu____23670 =
                     let uu____23671 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23671  in
                   if uu____23670
                   then
                     let val_decl =
                       let uu___132_23701 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___132_23701.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___132_23701.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___132_23701.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23702 = encode_sigelt' env1 val_decl  in
                     match uu____23702 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23644 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23736,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23738;
                          FStar_Syntax_Syntax.lbtyp = uu____23739;
                          FStar_Syntax_Syntax.lbeff = uu____23740;
                          FStar_Syntax_Syntax.lbdef = uu____23741;
                          FStar_Syntax_Syntax.lbattrs = uu____23742;
                          FStar_Syntax_Syntax.lbpos = uu____23743;_}::[]),uu____23744)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23761 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____23761 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23790 =
                   let uu____23793 =
                     let uu____23794 =
                       let uu____23801 =
                         let uu____23802 =
                           let uu____23813 =
                             let uu____23814 =
                               let uu____23819 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23819)  in
                             FStar_SMTEncoding_Util.mkEq uu____23814  in
                           ([[b2t_x]], [xx], uu____23813)  in
                         FStar_SMTEncoding_Util.mkForall uu____23802  in
                       (uu____23801,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23794  in
                   [uu____23793]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23790
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23840,uu____23841) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_23850  ->
                  match uu___100_23850 with
                  | FStar_Syntax_Syntax.Discriminator uu____23851 -> true
                  | uu____23852 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23853,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23864 =
                     let uu____23865 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23865.FStar_Ident.idText  in
                   uu____23864 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___101_23869  ->
                     match uu___101_23869 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23870 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23872) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___102_23883  ->
                  match uu___102_23883 with
                  | FStar_Syntax_Syntax.Projector uu____23884 -> true
                  | uu____23889 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23892 = try_lookup_free_var env l  in
          (match uu____23892 with
           | FStar_Pervasives_Native.Some uu____23899 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___133_23901 = se  in
                 let uu____23902 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____23902;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_23901.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_23901.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___133_23901.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23905) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23917) ->
          let uu____23926 = encode_sigelts env ses  in
          (match uu____23926 with
           | (g,env1) ->
               let uu____23943 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___103_23966  ->
                         match uu___103_23966 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23967;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23968;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23969;_}
                             -> false
                         | uu____23972 -> true))
                  in
               (match uu____23943 with
                | (g',inversions) ->
                    let uu____23987 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___104_24008  ->
                              match uu___104_24008 with
                              | FStar_SMTEncoding_Term.DeclFun uu____24009 ->
                                  true
                              | uu____24020 -> false))
                       in
                    (match uu____23987 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____24036,tps,k,uu____24039,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___105_24056  ->
                    match uu___105_24056 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____24057 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____24068 = c  in
              match uu____24068 with
              | (name,args,uu____24073,uu____24074,uu____24075) ->
                  let uu____24080 =
                    let uu____24081 =
                      let uu____24092 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____24115  ->
                                match uu____24115 with
                                | (uu____24122,sort,uu____24124) -> sort))
                         in
                      (name, uu____24092, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____24081  in
                  [uu____24080]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____24153 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____24159 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____24159 FStar_Option.isNone))
               in
            if uu____24153
            then []
            else
              (let uu____24191 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____24191 with
               | (xxsym,xx) ->
                   let uu____24200 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____24239  ->
                             fun l  ->
                               match uu____24239 with
                               | (out,decls) ->
                                   let uu____24259 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____24259 with
                                    | (uu____24270,data_t) ->
                                        let uu____24272 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____24272 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____24310 =
                                                 let uu____24311 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____24311.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____24310 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____24314,indices) ->
                                                   indices
                                               | uu____24336 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24360  ->
                                                         match uu____24360
                                                         with
                                                         | (x,uu____24366) ->
                                                             let uu____24367
                                                               =
                                                               let uu____24368
                                                                 =
                                                                 let uu____24375
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____24375,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24368
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____24367)
                                                    env)
                                                in
                                             let uu____24378 =
                                               encode_args indices env1  in
                                             (match uu____24378 with
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
                                                      let uu____24404 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____24420
                                                                 =
                                                                 let uu____24425
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____24425,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____24420)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____24404
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____24428 =
                                                      let uu____24429 =
                                                        let uu____24434 =
                                                          let uu____24435 =
                                                            let uu____24440 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____24440,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____24435
                                                           in
                                                        (out, uu____24434)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____24429
                                                       in
                                                    (uu____24428,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____24200 with
                    | (data_ax,decls) ->
                        let uu____24453 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____24453 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24464 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24464 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____24468 =
                                 let uu____24475 =
                                   let uu____24476 =
                                     let uu____24487 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24496 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24487,
                                       uu____24496)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24476
                                    in
                                 let uu____24505 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____24475,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24505)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____24468
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24506 =
            let uu____24519 =
              let uu____24520 = FStar_Syntax_Subst.compress k  in
              uu____24520.FStar_Syntax_Syntax.n  in
            match uu____24519 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24565 -> (tps, k)  in
          (match uu____24506 with
           | (formals,res) ->
               let uu____24588 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24588 with
                | (formals1,res1) ->
                    let uu____24599 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24599 with
                     | (vars,guards,env',binder_decls,uu____24624) ->
                         let arity = FStar_List.length vars  in
                         let uu____24638 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____24638 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24661 =
                                  let uu____24668 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24668)  in
                                FStar_SMTEncoding_Util.mkApp uu____24661  in
                              let uu____24673 =
                                let tname_decl =
                                  let uu____24683 =
                                    let uu____24684 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24708  ->
                                              match uu____24708 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24721 = varops.next_id ()  in
                                    (tname, uu____24684,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24721, false)
                                     in
                                  constructor_or_logic_type_decl uu____24683
                                   in
                                let uu____24724 =
                                  match vars with
                                  | [] ->
                                      let uu____24737 =
                                        let uu____24738 =
                                          let uu____24741 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____24741
                                           in
                                        replace_free_var env1 t arity tname
                                          uu____24738
                                         in
                                      ([], uu____24737)
                                  | uu____24752 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24759 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24759
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24773 =
                                          let uu____24780 =
                                            let uu____24781 =
                                              let uu____24796 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24796)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24781
                                             in
                                          (uu____24780,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24773
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24724 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24673 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24832 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24832 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24850 =
                                               let uu____24851 =
                                                 let uu____24858 =
                                                   let uu____24859 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24859
                                                    in
                                                 (uu____24858,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24851
                                                in
                                             [uu____24850]
                                           else []  in
                                         let uu____24861 =
                                           let uu____24864 =
                                             let uu____24867 =
                                               let uu____24868 =
                                                 let uu____24875 =
                                                   let uu____24876 =
                                                     let uu____24887 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24887)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24876
                                                    in
                                                 (uu____24875,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24868
                                                in
                                             [uu____24867]  in
                                           FStar_List.append karr uu____24864
                                            in
                                         FStar_List.append decls1 uu____24861
                                      in
                                   let aux =
                                     let uu____24899 =
                                       let uu____24902 =
                                         inversion_axioms tapp vars  in
                                       let uu____24905 =
                                         let uu____24908 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24908]  in
                                       FStar_List.append uu____24902
                                         uu____24905
                                        in
                                     FStar_List.append kindingAx uu____24899
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24913,uu____24914,uu____24915,uu____24916,uu____24917)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24923,t,uu____24925,n_tps,uu____24927) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24935 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____24935 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____24975 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____24975 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____24996 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24996 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____25010 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____25010 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____25068 =
                                            mk_term_projector_name d x  in
                                          (uu____25068,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____25072 =
                                  let uu____25073 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____25073, true)
                                   in
                                FStar_All.pipe_right uu____25072
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
                              let uu____25086 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____25086 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____25098::uu____25099 ->
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
                                         let uu____25126 =
                                           let uu____25137 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____25137)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____25126
                                     | uu____25156 -> tok_typing  in
                                   let uu____25159 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____25159 with
                                    | (vars',guards',env'',decls_formals,uu____25184)
                                        ->
                                        let uu____25197 =
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
                                        (match uu____25197 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25224 ->
                                                   let uu____25231 =
                                                     let uu____25232 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25232
                                                      in
                                                   [uu____25231]
                                                in
                                             let encode_elim uu____25246 =
                                               let uu____25247 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____25247 with
                                               | (head1,args) ->
                                                   let uu____25286 =
                                                     let uu____25287 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____25287.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____25286 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25299;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25300;_},uu____25301)
                                                        ->
                                                        let uu____25306 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25306
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25321
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25321
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
                                                                    uu____25372
                                                                    ->
                                                                    let uu____25373
                                                                    =
                                                                    let uu____25378
                                                                    =
                                                                    let uu____25379
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25379
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25378)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25373
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25395
                                                                    =
                                                                    let uu____25396
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25396
                                                                     in
                                                                    if
                                                                    uu____25395
                                                                    then
                                                                    let uu____25409
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25409]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25411
                                                                    =
                                                                    let uu____25424
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25474
                                                                     ->
                                                                    fun
                                                                    uu____25475
                                                                     ->
                                                                    match 
                                                                    (uu____25474,
                                                                    uu____25475)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25570
                                                                    =
                                                                    let uu____25577
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25577
                                                                     in
                                                                    (match uu____25570
                                                                    with
                                                                    | 
                                                                    (uu____25590,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25598
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25598
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25600
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25600
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
                                                                    uu____25424
                                                                     in
                                                                  (match uu____25411
                                                                   with
                                                                   | 
                                                                   (uu____25617,arg_vars,elim_eqns_or_guards,uu____25620)
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
                                                                    let uu____25644
                                                                    =
                                                                    let uu____25651
                                                                    =
                                                                    let uu____25652
                                                                    =
                                                                    let uu____25663
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25664
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    let uu____25670
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25670)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25665
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25663,
                                                                    uu____25664)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25652
                                                                     in
                                                                    (uu____25651,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25644
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____25680
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____25680
                                                                    then
                                                                    let x =
                                                                    let uu____25686
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25686,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25688
                                                                    =
                                                                    let uu____25695
                                                                    =
                                                                    let uu____25696
                                                                    =
                                                                    let uu____25707
                                                                    =
                                                                    let uu____25712
                                                                    =
                                                                    let uu____25715
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25715]
                                                                     in
                                                                    [uu____25712]
                                                                     in
                                                                    let uu____25720
                                                                    =
                                                                    let uu____25721
                                                                    =
                                                                    let uu____25726
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25726,
                                                                    uu____25727)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25721
                                                                     in
                                                                    (uu____25707,
                                                                    [x],
                                                                    uu____25720)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25696
                                                                     in
                                                                    let uu____25740
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25695,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25740)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25688
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25745
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
                                                                    (let uu____25777
                                                                    =
                                                                    let uu____25778
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25778
                                                                    dapp1  in
                                                                    [uu____25777])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25745
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25785
                                                                    =
                                                                    let uu____25792
                                                                    =
                                                                    let uu____25793
                                                                    =
                                                                    let uu____25804
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25805
                                                                    =
                                                                    let uu____25806
                                                                    =
                                                                    let uu____25811
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25811)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25806
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25804,
                                                                    uu____25805)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25793
                                                                     in
                                                                    (uu____25792,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25785)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____25823 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25823
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25838
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25838
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
                                                                    uu____25889
                                                                    ->
                                                                    let uu____25890
                                                                    =
                                                                    let uu____25895
                                                                    =
                                                                    let uu____25896
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25896
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25895)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25890
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25912
                                                                    =
                                                                    let uu____25913
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25913
                                                                     in
                                                                    if
                                                                    uu____25912
                                                                    then
                                                                    let uu____25926
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25926]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25928
                                                                    =
                                                                    let uu____25941
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25991
                                                                     ->
                                                                    fun
                                                                    uu____25992
                                                                     ->
                                                                    match 
                                                                    (uu____25991,
                                                                    uu____25992)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____26087
                                                                    =
                                                                    let uu____26094
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____26094
                                                                     in
                                                                    (match uu____26087
                                                                    with
                                                                    | 
                                                                    (uu____26107,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____26115
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____26115
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____26117
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____26117
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
                                                                    uu____25941
                                                                     in
                                                                  (match uu____25928
                                                                   with
                                                                   | 
                                                                   (uu____26134,arg_vars,elim_eqns_or_guards,uu____26137)
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
                                                                    let uu____26161
                                                                    =
                                                                    let uu____26168
                                                                    =
                                                                    let uu____26169
                                                                    =
                                                                    let uu____26180
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26181
                                                                    =
                                                                    let uu____26182
                                                                    =
                                                                    let uu____26187
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26187)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26182
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26180,
                                                                    uu____26181)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26169
                                                                     in
                                                                    (uu____26168,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26161
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26197
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26197
                                                                    then
                                                                    let x =
                                                                    let uu____26203
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26203,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26205
                                                                    =
                                                                    let uu____26212
                                                                    =
                                                                    let uu____26213
                                                                    =
                                                                    let uu____26224
                                                                    =
                                                                    let uu____26229
                                                                    =
                                                                    let uu____26232
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26232]
                                                                     in
                                                                    [uu____26229]
                                                                     in
                                                                    let uu____26237
                                                                    =
                                                                    let uu____26238
                                                                    =
                                                                    let uu____26243
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26244
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26243,
                                                                    uu____26244)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26238
                                                                     in
                                                                    (uu____26224,
                                                                    [x],
                                                                    uu____26237)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26213
                                                                     in
                                                                    let uu____26257
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26212,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26257)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26205
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26262
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
                                                                    (let uu____26294
                                                                    =
                                                                    let uu____26295
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26295
                                                                    dapp1  in
                                                                    [uu____26294])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26262
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26302
                                                                    =
                                                                    let uu____26309
                                                                    =
                                                                    let uu____26310
                                                                    =
                                                                    let uu____26321
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26322
                                                                    =
                                                                    let uu____26323
                                                                    =
                                                                    let uu____26328
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26328)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26323
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26321,
                                                                    uu____26322)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26310
                                                                     in
                                                                    (uu____26309,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26302)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____26339 ->
                                                        ((let uu____26341 =
                                                            let uu____26346 =
                                                              let uu____26347
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____26348
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____26347
                                                                uu____26348
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____26346)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26341);
                                                         ([], [])))
                                                in
                                             let uu____26353 = encode_elim ()
                                                in
                                             (match uu____26353 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26379 =
                                                      let uu____26382 =
                                                        let uu____26385 =
                                                          let uu____26388 =
                                                            let uu____26391 =
                                                              let uu____26392
                                                                =
                                                                let uu____26403
                                                                  =
                                                                  let uu____26404
                                                                    =
                                                                    let uu____26405
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26405
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26404
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26403)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26392
                                                               in
                                                            [uu____26391]  in
                                                          let uu____26408 =
                                                            let uu____26411 =
                                                              let uu____26414
                                                                =
                                                                let uu____26417
                                                                  =
                                                                  let uu____26420
                                                                    =
                                                                    let uu____26423
                                                                    =
                                                                    let uu____26426
                                                                    =
                                                                    let uu____26427
                                                                    =
                                                                    let uu____26434
                                                                    =
                                                                    let uu____26435
                                                                    =
                                                                    let uu____26446
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26446)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26435
                                                                     in
                                                                    (uu____26434,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26427
                                                                     in
                                                                    let uu____26455
                                                                    =
                                                                    let uu____26458
                                                                    =
                                                                    let uu____26459
                                                                    =
                                                                    let uu____26466
                                                                    =
                                                                    let uu____26467
                                                                    =
                                                                    let uu____26478
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____26479
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26478,
                                                                    uu____26479)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26467
                                                                     in
                                                                    (uu____26466,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26459
                                                                     in
                                                                    [uu____26458]
                                                                     in
                                                                    uu____26426
                                                                    ::
                                                                    uu____26455
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26423
                                                                     in
                                                                  FStar_List.append
                                                                    uu____26420
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26417
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26414
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26411
                                                             in
                                                          FStar_List.append
                                                            uu____26388
                                                            uu____26408
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____26385
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____26382
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26379
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
           (fun uu____26513  ->
              fun se  ->
                match uu____26513 with
                | (g,env1) ->
                    let uu____26533 = encode_sigelt env1 se  in
                    (match uu____26533 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26598 =
        match uu____26598 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____26630 ->
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
                 ((let uu____26636 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26636
                   then
                     let uu____26637 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26638 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26639 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26637 uu____26638 uu____26639
                   else ());
                  (let uu____26641 = encode_term t1 env1  in
                   match uu____26641 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26657 =
                         let uu____26664 =
                           let uu____26665 =
                             let uu____26666 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26666
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26665  in
                         new_term_constant_from_string env1 x uu____26664  in
                       (match uu____26657 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26680 = FStar_Options.log_queries ()
                                 in
                              if uu____26680
                              then
                                let uu____26681 =
                                  let uu____26682 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26683 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26684 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26682 uu____26683 uu____26684
                                   in
                                FStar_Pervasives_Native.Some uu____26681
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____26696,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26716 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26716 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26739 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26739 with | (uu____26762,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26775 'Auu____26776 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26775,'Auu____26776)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26845  ->
              match uu____26845 with
              | (l,uu____26857,uu____26858) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26902  ->
              match uu____26902 with
              | (l,uu____26916,uu____26917) ->
                  let uu____26926 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26927 =
                    let uu____26930 =
                      let uu____26931 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26931  in
                    [uu____26930]  in
                  uu____26926 :: uu____26927))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____26958 =
      let uu____26961 =
        let uu____26962 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____26965 =
          let uu____26966 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____26966 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26962;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26965
        }  in
      [uu____26961]  in
    FStar_ST.op_Colon_Equals last_env uu____26958
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____27004 = FStar_ST.op_Bang last_env  in
      match uu____27004 with
      | [] -> failwith "No env; call init first!"
      | e::uu____27035 ->
          let uu___134_27038 = e  in
          let uu____27039 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___134_27038.bindings);
            depth = (uu___134_27038.depth);
            tcenv;
            warn = (uu___134_27038.warn);
            cache = (uu___134_27038.cache);
            nolabels = (uu___134_27038.nolabels);
            use_zfuel_name = (uu___134_27038.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_27038.encode_non_total_function_typ);
            current_module_name = uu____27039
          }
  
let (set_env : env_t -> unit) =
  fun env  ->
    let uu____27045 = FStar_ST.op_Bang last_env  in
    match uu____27045 with
    | [] -> failwith "Empty env stack"
    | uu____27075::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____27110  ->
    let uu____27111 = FStar_ST.op_Bang last_env  in
    match uu____27111 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___135_27149 = hd1  in
          {
            bindings = (uu___135_27149.bindings);
            depth = (uu___135_27149.depth);
            tcenv = (uu___135_27149.tcenv);
            warn = (uu___135_27149.warn);
            cache = refs;
            nolabels = (uu___135_27149.nolabels);
            use_zfuel_name = (uu___135_27149.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___135_27149.encode_non_total_function_typ);
            current_module_name = (uu___135_27149.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____27181  ->
    let uu____27182 = FStar_ST.op_Bang last_env  in
    match uu____27182 with
    | [] -> failwith "Popping an empty stack"
    | uu____27212::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____27294::uu____27295,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___136_27303 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___136_27303.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___136_27303.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___136_27303.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27304 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____27323 =
        let uu____27326 =
          let uu____27327 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27327  in
        let uu____27328 = open_fact_db_tags env  in uu____27326 ::
          uu____27328
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27323
  
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
      let uu____27354 = encode_sigelt env se  in
      match uu____27354 with
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
        let uu____27398 = FStar_Options.log_queries ()  in
        if uu____27398
        then
          let uu____27401 =
            let uu____27402 =
              let uu____27403 =
                let uu____27404 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27404 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27403  in
            FStar_SMTEncoding_Term.Caption uu____27402  in
          uu____27401 :: decls
        else decls  in
      (let uu____27415 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27415
       then
         let uu____27416 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27416
       else ());
      (let env =
         let uu____27419 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____27419 tcenv  in
       let uu____27420 = encode_top_level_facts env se  in
       match uu____27420 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27434 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____27434)))
  
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
      (let uu____27450 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27450
       then
         let uu____27451 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27451
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27492  ->
                 fun se  ->
                   match uu____27492 with
                   | (g,env2) ->
                       let uu____27512 = encode_top_level_facts env2 se  in
                       (match uu____27512 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____27535 =
         encode_signature
           (let uu___137_27544 = env  in
            {
              bindings = (uu___137_27544.bindings);
              depth = (uu___137_27544.depth);
              tcenv = (uu___137_27544.tcenv);
              warn = false;
              cache = (uu___137_27544.cache);
              nolabels = (uu___137_27544.nolabels);
              use_zfuel_name = (uu___137_27544.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___137_27544.encode_non_total_function_typ);
              current_module_name = (uu___137_27544.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____27535 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27563 = FStar_Options.log_queries ()  in
             if uu____27563
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___138_27571 = env1  in
               {
                 bindings = (uu___138_27571.bindings);
                 depth = (uu___138_27571.depth);
                 tcenv = (uu___138_27571.tcenv);
                 warn = true;
                 cache = (uu___138_27571.cache);
                 nolabels = (uu___138_27571.nolabels);
                 use_zfuel_name = (uu___138_27571.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___138_27571.encode_non_total_function_typ);
                 current_module_name = (uu___138_27571.current_module_name)
               });
            (let uu____27573 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____27573
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
        (let uu____27631 =
           let uu____27632 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____27632.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27631);
        (let env =
           let uu____27634 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____27634 tcenv  in
         let uu____27635 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____27672 = aux rest  in
                 (match uu____27672 with
                  | (out,rest1) ->
                      let t =
                        let uu____27700 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27700 with
                        | FStar_Pervasives_Native.Some uu____27703 ->
                            let uu____27704 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27704
                              x.FStar_Syntax_Syntax.sort
                        | uu____27705 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27709 =
                        let uu____27712 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___139_27715 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___139_27715.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___139_27715.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27712 :: out  in
                      (uu____27709, rest1))
             | uu____27720 -> ([], bindings)  in
           let uu____27727 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____27727 with
           | (closing,bindings) ->
               let uu____27752 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27752, bindings)
            in
         match uu____27635 with
         | (q1,bindings) ->
             let uu____27775 = encode_env_bindings env bindings  in
             (match uu____27775 with
              | (env_decls,env1) ->
                  ((let uu____27797 =
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
                    if uu____27797
                    then
                      let uu____27798 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27798
                    else ());
                   (let uu____27800 = encode_formula q1 env1  in
                    match uu____27800 with
                    | (phi,qdecls) ->
                        let uu____27821 =
                          let uu____27826 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27826 phi
                           in
                        (match uu____27821 with
                         | (labels,phi1) ->
                             let uu____27843 = encode_labels labels  in
                             (match uu____27843 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27880 =
                                      let uu____27887 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27888 =
                                        varops.mk_unique "@query"  in
                                      (uu____27887,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27888)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27880
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
  