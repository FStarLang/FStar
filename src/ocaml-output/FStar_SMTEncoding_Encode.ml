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
              (let uu____3663 = FStar_Util.first_N arity args  in
               match uu____3663 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3686 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3686 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___92_3695  ->
    match uu___92_3695 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3696 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____3742;
                       FStar_SMTEncoding_Term.rng = uu____3743;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3766) ->
              let uu____3775 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3786 -> false) args (FStar_List.rev xs))
                 in
              if uu____3775
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3790,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3794 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3800 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3800))
                 in
              if uu____3794
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3804 -> FStar_Pervasives_Native.None  in
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
    | uu____4064 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____4070 -> false
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4097 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4110 ->
            let uu____4117 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____4117
        | uu____4118 ->
            if norm1
            then let uu____4119 = whnf env t1  in aux false uu____4119
            else
              (let uu____4121 =
                 let uu____4122 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____4123 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4122 uu____4123
                  in
               failwith uu____4121)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4157) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4162 ->
        let uu____4163 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4163)
  
let is_arithmetic_primitive :
  'Auu____4180 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4180 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4202::uu____4203::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4207::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4210 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4233 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4250 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4257 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4257)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4298)::uu____4299::uu____4300::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4351)::uu____4352::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4389 -> false
  
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
          let uu____4698 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4698, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4701 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4701, [])
      | FStar_Const.Const_char c1 ->
          let uu____4705 =
            let uu____4706 =
              let uu____4713 =
                let uu____4716 =
                  let uu____4717 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4717  in
                [uu____4716]  in
              ("FStar.Char.__char_of_int", uu____4713)  in
            FStar_SMTEncoding_Util.mkApp uu____4706  in
          (uu____4705, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4733 =
            let uu____4734 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4734  in
          (uu____4733, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4755) ->
          let uu____4756 = varops.string_const s  in (uu____4756, [])
      | FStar_Const.Const_range uu____4759 ->
          let uu____4760 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4760, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4766 =
            let uu____4767 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4767  in
          failwith uu____4766

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
        (let uu____4796 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4796
         then
           let uu____4797 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4797
         else ());
        (let uu____4799 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4889  ->
                   fun b  ->
                     match uu____4889 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4968 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4984 = gen_term_var env1 x  in
                           match uu____4984 with
                           | (xxsym,xx,env') ->
                               let uu____5008 =
                                 let uu____5013 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____5013 env1 xx
                                  in
                               (match uu____5008 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4968 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4799 with
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
          let uu____5162 = encode_term t env  in
          match uu____5162 with
          | (t1,decls) ->
              let uu____5173 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5173, decls)

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
          let uu____5184 = encode_term t env  in
          match uu____5184 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5199 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5199, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5201 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5201, decls))

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
        let uu____5207 = encode_args args_e env  in
        match uu____5207 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5226 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5237 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5237  in
            let binary arg_tms1 =
              let uu____5252 =
                let uu____5253 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5253  in
              let uu____5254 =
                let uu____5255 =
                  let uu____5256 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5256  in
                FStar_SMTEncoding_Term.unboxInt uu____5255  in
              (uu____5252, uu____5254)  in
            let mk_default uu____5264 =
              let uu____5265 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5265 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____5327 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5327
              then
                let uu____5328 =
                  let uu____5329 = mk_args ts  in op uu____5329  in
                FStar_All.pipe_right uu____5328 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5364 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5364
              then
                let uu____5365 = binary ts  in
                match uu____5365 with
                | (t1,t2) ->
                    let uu____5372 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5372
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5376 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5376
                 then
                   let uu____5377 =
                     let uu____5378 = binary ts  in op uu____5378  in
                   FStar_All.pipe_right uu____5377
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
            let uu____5539 =
              let uu____5549 =
                FStar_List.tryFind
                  (fun uu____5573  ->
                     match uu____5573 with
                     | (l,uu____5583) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5549 FStar_Util.must  in
            (match uu____5539 with
             | (uu____5627,op) ->
                 let uu____5639 = op arg_tms  in (uu____5639, decls))

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
        let uu____5653 = FStar_List.hd args_e  in
        match uu____5653 with
        | (tm_sz,uu____5667) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5677 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5677 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____5685 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5685);
                   t_decls1)
               in
            let uu____5686 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5724::(sz_arg,uu____5726)::uu____5727::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5776 =
                    let uu____5785 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5785  in
                  let uu____5806 =
                    let uu____5809 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5809  in
                  (uu____5776, uu____5806)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5821::(sz_arg,uu____5823)::uu____5824::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5873 =
                    let uu____5874 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5874
                     in
                  failwith uu____5873
              | uu____5889 ->
                  let uu____5902 = FStar_List.tail args_e  in
                  (uu____5902, FStar_Pervasives_Native.None)
               in
            (match uu____5686 with
             | (arg_tms,ext_sz) ->
                 let uu____5955 = encode_args arg_tms env  in
                 (match uu____5955 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5976 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5987 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5987  in
                      let unary_arith arg_tms2 =
                        let uu____5998 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5998  in
                      let binary arg_tms2 =
                        let uu____6013 =
                          let uu____6014 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____6014
                           in
                        let uu____6015 =
                          let uu____6016 =
                            let uu____6017 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____6017  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____6016
                           in
                        (uu____6013, uu____6015)  in
                      let binary_arith arg_tms2 =
                        let uu____6034 =
                          let uu____6035 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____6035
                           in
                        let uu____6036 =
                          let uu____6037 =
                            let uu____6038 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____6038  in
                          FStar_SMTEncoding_Term.unboxInt uu____6037  in
                        (uu____6034, uu____6036)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____6096 =
                          let uu____6097 = mk_args ts  in op uu____6097  in
                        FStar_All.pipe_right uu____6096 resBox  in
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
                        let uu____6229 =
                          let uu____6234 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____6234  in
                        let uu____6236 =
                          let uu____6241 =
                            let uu____6242 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____6242  in
                          FStar_SMTEncoding_Term.boxBitVec uu____6241  in
                        mk_bv uu____6229 unary uu____6236 arg_tms2  in
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
                      let uu____6475 =
                        let uu____6485 =
                          FStar_List.tryFind
                            (fun uu____6509  ->
                               match uu____6509 with
                               | (l,uu____6519) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6485 FStar_Util.must  in
                      (match uu____6475 with
                       | (uu____6565,op) ->
                           let uu____6577 = op arg_tms1  in
                           (uu____6577, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6588 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6588
       then
         let uu____6589 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6590 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6591 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6589 uu____6590
           uu____6591
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6597 ->
           let uu____6622 =
             let uu____6623 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6624 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6625 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6626 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6623
               uu____6624 uu____6625 uu____6626
              in
           failwith uu____6622
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6631 =
             let uu____6632 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6633 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6634 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6635 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6632
               uu____6633 uu____6634 uu____6635
              in
           failwith uu____6631
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6641 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____6641 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6643 =
             let uu____6644 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6644
              in
           failwith uu____6643
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____6651),uu____6652) ->
           let uu____6701 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____6709 -> false  in
           if uu____6701
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____6724) ->
           let tv =
             let uu____6730 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____6730
              in
           let t1 =
             let uu____6734 =
               let uu____6743 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____6743]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____6734
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6763) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6771 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6771, [])
       | FStar_Syntax_Syntax.Tm_type uu____6772 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6774) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6799 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6799 with
            | (binders1,res) ->
                let uu____6810 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6810
                then
                  let uu____6815 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6815 with
                   | (vars,guards,env',decls,uu____6840) ->
                       let fsym =
                         let uu____6858 = varops.fresh "f"  in
                         (uu____6858, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6861 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___114_6870 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___114_6870.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___114_6870.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___114_6870.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___114_6870.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___114_6870.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___114_6870.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___114_6870.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___114_6870.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___114_6870.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___114_6870.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___114_6870.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___114_6870.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___114_6870.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___114_6870.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___114_6870.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___114_6870.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___114_6870.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___114_6870.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___114_6870.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___114_6870.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___114_6870.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___114_6870.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___114_6870.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___114_6870.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___114_6870.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___114_6870.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___114_6870.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___114_6870.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___114_6870.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___114_6870.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___114_6870.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___114_6870.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___114_6870.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___114_6870.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___114_6870.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___114_6870.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___114_6870.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6861 with
                        | (pre_opt,res_t) ->
                            let uu____6881 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6881 with
                             | (res_pred,decls') ->
                                 let uu____6892 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6901 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6901, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6903 =
                                         encode_formula pre env'  in
                                       (match uu____6903 with
                                        | (guard,decls0) ->
                                            let uu____6914 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6914, decls0))
                                    in
                                 (match uu____6892 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6922 =
                                          let uu____6933 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6933)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6922
                                         in
                                      let cvars =
                                        let uu____6949 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6949
                                          (FStar_List.filter
                                             (fun uu____6975  ->
                                                match uu____6975 with
                                                | (x,uu____6981) ->
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
                                      let uu____6994 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6994 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____7002 =
                                             let uu____7003 =
                                               let uu____7010 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____7010)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7003
                                              in
                                           (uu____7002,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____7028 =
                                               let uu____7029 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____7029
                                                in
                                             varops.mk_unique uu____7028  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____7038 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____7038
                                             then
                                               let uu____7039 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7039
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
                                             let uu____7045 =
                                               let uu____7052 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____7052)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7045
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
                                             let uu____7064 =
                                               let uu____7071 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____7071,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7064
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
                                             let uu____7084 =
                                               let uu____7091 =
                                                 let uu____7092 =
                                                   let uu____7103 =
                                                     let uu____7104 =
                                                       let uu____7109 =
                                                         let uu____7110 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____7110
                                                          in
                                                       (f_has_t, uu____7109)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____7104
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____7103)
                                                    in
                                                 mkForall_fuel uu____7092  in
                                               (uu____7091,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7084
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____7125 =
                                               let uu____7132 =
                                                 let uu____7133 =
                                                   let uu____7144 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____7144)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____7133
                                                  in
                                               (uu____7132,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7125
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
                                           ((let uu____7161 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____7161);
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
                     let uu____7172 =
                       let uu____7179 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____7179,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7172  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____7189 =
                       let uu____7196 =
                         let uu____7197 =
                           let uu____7208 =
                             let uu____7209 =
                               let uu____7214 =
                                 let uu____7215 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____7215
                                  in
                               (f_has_t, uu____7214)  in
                             FStar_SMTEncoding_Util.mkImp uu____7209  in
                           ([[f_has_t]], [fsym], uu____7208)  in
                         mkForall_fuel uu____7197  in
                       (uu____7196, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7189  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____7232 ->
           let uu____7239 =
             let uu____7244 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____7244 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____7251;
                 FStar_Syntax_Syntax.vars = uu____7252;_} ->
                 let uu____7259 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____7259 with
                  | (b,f1) ->
                      let uu____7278 =
                        let uu____7279 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7279  in
                      (uu____7278, f1))
             | uu____7288 -> failwith "impossible"  in
           (match uu____7239 with
            | (x,f) ->
                let uu____7299 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7299 with
                 | (base_t,decls) ->
                     let uu____7310 = gen_term_var env x  in
                     (match uu____7310 with
                      | (x1,xtm,env') ->
                          let uu____7324 = encode_formula f env'  in
                          (match uu____7324 with
                           | (refinement,decls') ->
                               let uu____7335 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7335 with
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
                                      let uu____7355 =
                                        let uu____7362 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7369 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7362
                                          uu____7369
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7355
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7410  ->
                                              match uu____7410 with
                                              | (y,uu____7416) ->
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
                                    let uu____7443 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7443 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7451 =
                                           let uu____7452 =
                                             let uu____7459 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7459)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7452
                                            in
                                         (uu____7451,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7478 =
                                             let uu____7479 =
                                               let uu____7480 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7480
                                                in
                                             Prims.strcat module_name
                                               uu____7479
                                              in
                                           varops.mk_unique uu____7478  in
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
                                           let uu____7492 =
                                             let uu____7499 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7499)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7492
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
                                           let uu____7514 =
                                             let uu____7521 =
                                               let uu____7522 =
                                                 let uu____7533 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7533)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7522
                                                in
                                             (uu____7521,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7514
                                            in
                                         let t_kinding =
                                           let uu____7543 =
                                             let uu____7550 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7550,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7543
                                            in
                                         let t_interp =
                                           let uu____7560 =
                                             let uu____7567 =
                                               let uu____7568 =
                                                 let uu____7579 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7579)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7568
                                                in
                                             let uu____7596 =
                                               let uu____7597 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7597
                                                in
                                             (uu____7567, uu____7596,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7560
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7602 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7602);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar uv ->
           let ttm =
             let uu____7605 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7605  in
           let uu____7606 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____7606 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7618 =
                    let uu____7625 =
                      let uu____7626 =
                        let uu____7627 =
                          let uu____7628 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7628
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7627  in
                      varops.mk_unique uu____7626  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7625)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7618  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7629 ->
           let uu____7644 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7644 with
            | (head1,args_e) ->
                let uu____7679 =
                  let uu____7692 =
                    let uu____7693 = FStar_Syntax_Subst.compress head1  in
                    uu____7693.FStar_Syntax_Syntax.n  in
                  (uu____7692, args_e)  in
                (match uu____7679 with
                 | uu____7708 when head_redex env head1 ->
                     let uu____7721 = whnf env t  in
                     encode_term uu____7721 env
                 | uu____7722 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7741 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7755;
                       FStar_Syntax_Syntax.vars = uu____7756;_},uu____7757),uu____7758::
                    (v1,uu____7760)::(v2,uu____7762)::[]) when
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
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7837::(v1,uu____7839)::(v2,uu____7841)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7888 = encode_term v1 env  in
                     (match uu____7888 with
                      | (v11,decls1) ->
                          let uu____7899 = encode_term v2 env  in
                          (match uu____7899 with
                           | (v21,decls2) ->
                               let uu____7910 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7910,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7912)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7938)::(rng,uu____7940)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7975) ->
                     let e0 =
                       let uu____7993 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7993
                        in
                     ((let uu____8001 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____8001
                       then
                         let uu____8002 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____8002
                       else ());
                      (let e =
                         let uu____8007 =
                           let uu____8012 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____8013 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____8012
                             uu____8013
                            in
                         uu____8007 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____8022),(arg,uu____8024)::[]) -> encode_term arg env
                 | uu____8049 ->
                     let uu____8062 = encode_args args_e env  in
                     (match uu____8062 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____8119 = encode_term head1 env  in
                            match uu____8119 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____8183 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____8183 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8261  ->
                                                 fun uu____8262  ->
                                                   match (uu____8261,
                                                           uu____8262)
                                                   with
                                                   | ((bv,uu____8284),
                                                      (a,uu____8286)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8304 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8304
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8305 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8305 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8320 =
                                                   let uu____8327 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8336 =
                                                     let uu____8337 =
                                                       let uu____8338 =
                                                         let uu____8339 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8339
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8338
                                                        in
                                                     varops.mk_unique
                                                       uu____8337
                                                      in
                                                   (uu____8327,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8336)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8320
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8356 = lookup_free_var_sym env fv  in
                            match uu____8356 with
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
                                   FStar_Syntax_Syntax.pos = uu____8388;
                                   FStar_Syntax_Syntax.vars = uu____8389;_},uu____8390)
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
                                   FStar_Syntax_Syntax.pos = uu____8401;
                                   FStar_Syntax_Syntax.vars = uu____8402;_},uu____8403)
                                ->
                                let uu____8408 =
                                  let uu____8409 =
                                    let uu____8414 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8414
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8409
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8408
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8444 =
                                  let uu____8445 =
                                    let uu____8450 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8450
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8445
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8444
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8479,(FStar_Util.Inl t1,uu____8481),uu____8482)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8531,(FStar_Util.Inr c,uu____8533),uu____8534)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8583 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8610 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8610
                                  in
                               let uu____8611 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8611 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8627;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8628;_},uu____8629)
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
                                     | uu____8643 ->
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
           let uu____8708 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8708 with
            | (bs1,body1,opening) ->
                let fallback uu____8733 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8738 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8738, [decl])  in
                let is_impure rc =
                  let uu____8747 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8747 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8759 =
                          let uu____8772 =
                            FStar_TypeChecker_Env.get_range env.tcenv  in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8772 env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8759 with
                         | (t1,uu____8774,uu____8775) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8793 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8793
                  then
                    let uu____8796 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8796
                  else
                    (let uu____8798 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8798
                     then
                       let uu____8801 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8801
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8808 =
                         let uu____8813 =
                           let uu____8814 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8814
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8813)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8808);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8816 =
                       (is_impure rc) &&
                         (let uu____8818 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8818)
                        in
                     if uu____8816
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8825 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8825 with
                        | (vars,guards,envbody,decls,uu____8850) ->
                            let body2 =
                              let uu____8864 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8864
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8866 = encode_term body2 envbody  in
                            (match uu____8866 with
                             | (body3,decls') ->
                                 let uu____8877 =
                                   let uu____8884 = codomain_eff rc  in
                                   match uu____8884 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8899 = encode_term tfun env
                                          in
                                       (match uu____8899 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8877 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8925 =
                                          let uu____8936 =
                                            let uu____8937 =
                                              let uu____8942 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8942, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8937
                                             in
                                          ([], vars, uu____8936)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8925
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
                                            let uu____8956 =
                                              let uu____8963 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8963
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8956
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8986 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8986 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8994 =
                                             let uu____8995 =
                                               let uu____9002 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____9002)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8995
                                              in
                                           (uu____8994,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____9011 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____9011 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____9020 =
                                                    let uu____9021 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____9021 = cache_size
                                                     in
                                                  if uu____9020
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
                                                    let uu____9033 =
                                                      let uu____9034 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____9034
                                                       in
                                                    varops.mk_unique
                                                      uu____9033
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
                                                  let uu____9039 =
                                                    let uu____9046 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____9046)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____9039
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
                                                      let uu____9064 =
                                                        let uu____9065 =
                                                          let uu____9072 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____9072,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____9065
                                                         in
                                                      [uu____9064]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____9083 =
                                                    let uu____9090 =
                                                      let uu____9091 =
                                                        let uu____9102 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____9102)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____9091
                                                       in
                                                    (uu____9090,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____9083
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
                                                ((let uu____9115 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____9115);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____9116,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____9117;
                          FStar_Syntax_Syntax.lbunivs = uu____9118;
                          FStar_Syntax_Syntax.lbtyp = uu____9119;
                          FStar_Syntax_Syntax.lbeff = uu____9120;
                          FStar_Syntax_Syntax.lbdef = uu____9121;
                          FStar_Syntax_Syntax.lbattrs = uu____9122;
                          FStar_Syntax_Syntax.lbpos = uu____9123;_}::uu____9124),uu____9125)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____9155;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____9157;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____9159;
                FStar_Syntax_Syntax.lbpos = uu____9160;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____9184 ->
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
              let uu____9254 =
                let uu____9259 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9259 env  in
              match uu____9254 with
              | (ee1,decls1) ->
                  let uu____9284 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9284 with
                   | (xs,e21) ->
                       let uu____9303 = FStar_List.hd xs  in
                       (match uu____9303 with
                        | (x1,uu____9317) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9319 = encode_body e21 env'  in
                            (match uu____9319 with
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
            let uu____9349 =
              let uu____9356 =
                let uu____9357 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9357  in
              gen_term_var env uu____9356  in
            match uu____9349 with
            | (scrsym,scr',env1) ->
                let uu____9365 = encode_term e env1  in
                (match uu____9365 with
                 | (scr,decls) ->
                     let uu____9376 =
                       let encode_branch b uu____9405 =
                         match uu____9405 with
                         | (else_case,decls1) ->
                             let uu____9424 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9424 with
                              | (p,w,br) ->
                                  let uu____9450 = encode_pat env1 p  in
                                  (match uu____9450 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9487  ->
                                                   match uu____9487 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9494 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9510 =
                                               encode_term w1 env2  in
                                             (match uu____9510 with
                                              | (w2,decls2) ->
                                                  let uu____9521 =
                                                    let uu____9522 =
                                                      let uu____9527 =
                                                        let uu____9528 =
                                                          let uu____9533 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9533)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9528
                                                         in
                                                      (guard, uu____9527)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9522
                                                     in
                                                  (uu____9521, decls2))
                                          in
                                       (match uu____9494 with
                                        | (guard1,decls2) ->
                                            let uu____9542 =
                                              encode_br br env2  in
                                            (match uu____9542 with
                                             | (br1,decls3) ->
                                                 let uu____9555 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9555,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9376 with
                      | (match_tm,decls1) ->
                          let uu____9576 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9576, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____9598 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9598
       then
         let uu____9599 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9599
       else ());
      (let uu____9601 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9601 with
       | (vars,pat_term) ->
           let uu____9618 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9671  ->
                     fun v1  ->
                       match uu____9671 with
                       | (env1,vars1) ->
                           let uu____9723 = gen_term_var env1 v1  in
                           (match uu____9723 with
                            | (xx,uu____9745,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9618 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9828 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9829 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9830 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9838 = encode_const c env1  in
                      (match uu____9838 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9852::uu____9853 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9856 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9879 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9879 with
                        | (uu____9886,uu____9887::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9890 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9923  ->
                                  match uu____9923 with
                                  | (arg,uu____9931) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9937 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9937))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9968) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9999 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____10022 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____10066  ->
                                  match uu____10066 with
                                  | (arg,uu____10080) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____10086 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____10086))
                         in
                      FStar_All.pipe_right uu____10022 FStar_List.flatten
                   in
                let pat_term1 uu____10116 = encode_term pat_term env1  in
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
      let uu____10126 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10170  ->
                fun uu____10171  ->
                  match (uu____10170, uu____10171) with
                  | ((tms,decls),(t,uu____10207)) ->
                      let uu____10228 = encode_term t env  in
                      (match uu____10228 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10126 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10285 = FStar_Syntax_Util.list_elements e  in
        match uu____10285 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____10308 =
          let uu____10321 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10321 FStar_Syntax_Util.head_and_args
           in
        match uu____10308 with
        | (head1,args) ->
            let uu____10354 =
              let uu____10367 =
                let uu____10368 = FStar_Syntax_Util.un_uinst head1  in
                uu____10368.FStar_Syntax_Syntax.n  in
              (uu____10367, args)  in
            (match uu____10354 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10382,uu____10383)::(e,uu____10385)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10420 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____10460 =
            let uu____10473 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10473 FStar_Syntax_Util.head_and_args
             in
          match uu____10460 with
          | (head1,args) ->
              let uu____10508 =
                let uu____10521 =
                  let uu____10522 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10522.FStar_Syntax_Syntax.n  in
                (uu____10521, args)  in
              (match uu____10508 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10539)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10566 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10588 = smt_pat_or t1  in
            (match uu____10588 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10604 = list_elements1 e  in
                 FStar_All.pipe_right uu____10604
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10622 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10622
                           (FStar_List.map one_pat)))
             | uu____10633 ->
                 let uu____10638 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10638])
        | uu____10659 ->
            let uu____10662 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10662]
         in
      let uu____10683 =
        let uu____10702 =
          let uu____10703 = FStar_Syntax_Subst.compress t  in
          uu____10703.FStar_Syntax_Syntax.n  in
        match uu____10702 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10742 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10742 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10785;
                        FStar_Syntax_Syntax.effect_name = uu____10786;
                        FStar_Syntax_Syntax.result_typ = uu____10787;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10789)::(post,uu____10791)::(pats,uu____10793)::[];
                        FStar_Syntax_Syntax.flags = uu____10794;_}
                      ->
                      let uu____10835 = lemma_pats pats  in
                      (binders1, pre, post, uu____10835)
                  | uu____10852 -> failwith "impos"))
        | uu____10871 -> failwith "Impos"  in
      match uu____10683 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___115_10919 = env  in
            {
              bindings = (uu___115_10919.bindings);
              depth = (uu___115_10919.depth);
              tcenv = (uu___115_10919.tcenv);
              warn = (uu___115_10919.warn);
              cache = (uu___115_10919.cache);
              nolabels = (uu___115_10919.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___115_10919.encode_non_total_function_typ);
              current_module_name = (uu___115_10919.current_module_name)
            }  in
          let uu____10920 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10920 with
           | (vars,guards,env2,decls,uu____10945) ->
               let uu____10958 =
                 let uu____10973 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____11027 =
                             let uu____11038 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____11038
                               FStar_List.unzip
                              in
                           match uu____11027 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10973 FStar_List.unzip  in
               (match uu____10958 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___116_11190 = env2  in
                      {
                        bindings = (uu___116_11190.bindings);
                        depth = (uu___116_11190.depth);
                        tcenv = (uu___116_11190.tcenv);
                        warn = (uu___116_11190.warn);
                        cache = (uu___116_11190.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___116_11190.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___116_11190.encode_non_total_function_typ);
                        current_module_name =
                          (uu___116_11190.current_module_name)
                      }  in
                    let uu____11191 =
                      let uu____11196 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____11196 env3  in
                    (match uu____11191 with
                     | (pre1,decls'') ->
                         let uu____11203 =
                           let uu____11208 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____11208 env3  in
                         (match uu____11203 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____11218 =
                                let uu____11219 =
                                  let uu____11230 =
                                    let uu____11231 =
                                      let uu____11236 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____11236, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____11231
                                     in
                                  (pats, vars, uu____11230)  in
                                FStar_SMTEncoding_Util.mkForall uu____11219
                                 in
                              (uu____11218, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11245 = FStar_Syntax_Util.head_and_args t  in
      match uu____11245 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11298::(x,uu____11300)::(t1,uu____11302)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11349 = encode_term x env  in
               (match uu____11349 with
                | (x1,decls) ->
                    let uu____11362 = encode_term t1 env  in
                    (match uu____11362 with
                     | (t2,decls') ->
                         let uu____11375 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11375, (FStar_List.append decls decls'))))
           | uu____11378 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11403 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11403
        then
          let uu____11404 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11405 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11404 uu____11405
        else ()  in
      let enc f r l =
        let uu____11444 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11472 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11472 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11444 with
        | (decls,args) ->
            let uu____11501 =
              let uu___117_11502 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11502.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11502.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11501, decls)
         in
      let const_op f r uu____11527 =
        let uu____11530 = f r  in (uu____11530, [])  in
      let un_op f l =
        let uu____11553 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11553  in
      let bin_op f uu___93_11573 =
        match uu___93_11573 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11584 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11624 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11647  ->
                 match uu____11647 with
                 | (t,uu____11661) ->
                     let uu____11662 = encode_formula t env  in
                     (match uu____11662 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11624 with
        | (decls,phis) ->
            let uu____11691 =
              let uu___118_11692 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___118_11692.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___118_11692.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11691, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11755  ->
               match uu____11755 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11774) -> false
                    | uu____11775 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11791 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11791
        else
          (let uu____11805 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11805 r rf)
         in
      let mk_imp1 r uu___94_11840 =
        match uu___94_11840 with
        | (lhs,uu____11846)::(rhs,uu____11848)::[] ->
            let uu____11875 = encode_formula rhs env  in
            (match uu____11875 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11890) ->
                      (l1, decls1)
                  | uu____11895 ->
                      let uu____11896 = encode_formula lhs env  in
                      (match uu____11896 with
                       | (l2,decls2) ->
                           let uu____11907 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11907, (FStar_List.append decls1 decls2)))))
        | uu____11908 -> failwith "impossible"  in
      let mk_ite r uu___95_11935 =
        match uu___95_11935 with
        | (guard,uu____11941)::(_then,uu____11943)::(_else,uu____11945)::[]
            ->
            let uu____11982 = encode_formula guard env  in
            (match uu____11982 with
             | (g,decls1) ->
                 let uu____11993 = encode_formula _then env  in
                 (match uu____11993 with
                  | (t,decls2) ->
                      let uu____12004 = encode_formula _else env  in
                      (match uu____12004 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____12016 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____12045 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____12045  in
      let connectives =
        let uu____12065 =
          let uu____12080 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____12080)  in
        let uu____12103 =
          let uu____12120 =
            let uu____12135 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____12135)  in
          let uu____12158 =
            let uu____12175 =
              let uu____12192 =
                let uu____12207 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12207)  in
              let uu____12230 =
                let uu____12247 =
                  let uu____12264 =
                    let uu____12279 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12279)  in
                  [uu____12264;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12247  in
              uu____12192 :: uu____12230  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____12175  in
          uu____12120 :: uu____12158  in
        uu____12065 :: uu____12103  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12542 = encode_formula phi' env  in
            (match uu____12542 with
             | (phi2,decls) ->
                 let uu____12553 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12553, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12554 ->
            let uu____12561 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12561 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12600 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12600 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12612;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12614;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12616;
                 FStar_Syntax_Syntax.lbpos = uu____12617;_}::[]),e2)
            ->
            let uu____12641 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12641 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12688::(x,uu____12690)::(t,uu____12692)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12739 = encode_term x env  in
                 (match uu____12739 with
                  | (x1,decls) ->
                      let uu____12750 = encode_term t env  in
                      (match uu____12750 with
                       | (t1,decls') ->
                           let uu____12761 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12761, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12766)::(msg,uu____12768)::(phi2,uu____12770)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12815 =
                   let uu____12820 =
                     let uu____12821 = FStar_Syntax_Subst.compress r  in
                     uu____12821.FStar_Syntax_Syntax.n  in
                   let uu____12824 =
                     let uu____12825 = FStar_Syntax_Subst.compress msg  in
                     uu____12825.FStar_Syntax_Syntax.n  in
                   (uu____12820, uu____12824)  in
                 (match uu____12815 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12834))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12840 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12847)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12872 when head_redex env head2 ->
                 let uu____12885 = whnf env phi1  in
                 encode_formula uu____12885 env
             | uu____12886 ->
                 let uu____12899 = encode_term phi1 env  in
                 (match uu____12899 with
                  | (tt,decls) ->
                      let uu____12910 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___119_12913 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___119_12913.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___119_12913.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12910, decls)))
        | uu____12914 ->
            let uu____12915 = encode_term phi1 env  in
            (match uu____12915 with
             | (tt,decls) ->
                 let uu____12926 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___120_12929 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___120_12929.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___120_12929.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12926, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12973 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12973 with
        | (vars,guards,env2,decls,uu____13012) ->
            let uu____13025 =
              let uu____13038 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____13098 =
                          let uu____13109 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____13149  ->
                                    match uu____13149 with
                                    | (t,uu____13163) ->
                                        encode_smt_pattern t
                                          (let uu___121_13169 = env2  in
                                           {
                                             bindings =
                                               (uu___121_13169.bindings);
                                             depth = (uu___121_13169.depth);
                                             tcenv = (uu___121_13169.tcenv);
                                             warn = (uu___121_13169.warn);
                                             cache = (uu___121_13169.cache);
                                             nolabels =
                                               (uu___121_13169.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___121_13169.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___121_13169.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____13109 FStar_List.unzip
                           in
                        match uu____13098 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____13038 FStar_List.unzip  in
            (match uu____13025 with
             | (pats,decls') ->
                 let uu____13278 = encode_formula body env2  in
                 (match uu____13278 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13310;
                             FStar_SMTEncoding_Term.rng = uu____13311;_}::[])::[]
                            when
                            let uu____13326 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13326 = gf -> []
                        | uu____13327 -> guards  in
                      let uu____13332 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13332, body1,
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
                (fun uu____13396  ->
                   match uu____13396 with
                   | (x,uu____13402) ->
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
               let uu____13410 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13422 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____13422) uu____13410 tl1
                in
             let uu____13425 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13452  ->
                       match uu____13452 with
                       | (b,uu____13458) ->
                           let uu____13459 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____13459))
                in
             (match uu____13425 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13465) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____13479 =
                    let uu____13484 =
                      let uu____13485 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13485
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13484)
                     in
                  FStar_Errors.log_issue pos uu____13479)
          in
       let uu____13486 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13486 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13495 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13561  ->
                     match uu____13561 with
                     | (l,uu____13575) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13495 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13614,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13668 = encode_q_body env vars pats body  in
             match uu____13668 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13713 =
                     let uu____13724 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13724)  in
                   FStar_SMTEncoding_Term.mkForall uu____13713
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13747 = encode_q_body env vars pats body  in
             match uu____13747 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13791 =
                   let uu____13792 =
                     let uu____13803 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13803)  in
                   FStar_SMTEncoding_Term.mkExists uu____13792
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13791, decls))))

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
  let uu____13926 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13926 with
  | (asym,a) ->
      let uu____13933 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13933 with
       | (xsym,x) ->
           let uu____13940 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13940 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13994 =
                      let uu____14005 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____14005, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13994  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____14027 =
                      let uu____14034 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____14034)  in
                    FStar_SMTEncoding_Util.mkApp uu____14027  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____14047 =
                    let uu____14050 =
                      let uu____14053 =
                        let uu____14056 =
                          let uu____14057 =
                            let uu____14064 =
                              let uu____14065 =
                                let uu____14076 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____14076)  in
                              FStar_SMTEncoding_Util.mkForall uu____14065  in
                            (uu____14064, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____14057  in
                        let uu____14085 =
                          let uu____14088 =
                            let uu____14089 =
                              let uu____14096 =
                                let uu____14097 =
                                  let uu____14108 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____14108)  in
                                FStar_SMTEncoding_Util.mkForall uu____14097
                                 in
                              (uu____14096,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____14089  in
                          [uu____14088]  in
                        uu____14056 :: uu____14085  in
                      xtok_decl :: uu____14053  in
                    xname_decl :: uu____14050  in
                  (xtok1, (FStar_List.length vars), uu____14047)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____14198 =
                    let uu____14214 =
                      let uu____14227 =
                        let uu____14228 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____14228
                         in
                      quant axy uu____14227  in
                    (FStar_Parser_Const.op_Eq, uu____14214)  in
                  let uu____14240 =
                    let uu____14258 =
                      let uu____14274 =
                        let uu____14287 =
                          let uu____14288 =
                            let uu____14289 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14289  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14288
                           in
                        quant axy uu____14287  in
                      (FStar_Parser_Const.op_notEq, uu____14274)  in
                    let uu____14301 =
                      let uu____14319 =
                        let uu____14335 =
                          let uu____14348 =
                            let uu____14349 =
                              let uu____14350 =
                                let uu____14355 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14356 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14355, uu____14356)  in
                              FStar_SMTEncoding_Util.mkLT uu____14350  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14349
                             in
                          quant xy uu____14348  in
                        (FStar_Parser_Const.op_LT, uu____14335)  in
                      let uu____14368 =
                        let uu____14386 =
                          let uu____14402 =
                            let uu____14415 =
                              let uu____14416 =
                                let uu____14417 =
                                  let uu____14422 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14423 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14422, uu____14423)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14417  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14416
                               in
                            quant xy uu____14415  in
                          (FStar_Parser_Const.op_LTE, uu____14402)  in
                        let uu____14435 =
                          let uu____14453 =
                            let uu____14469 =
                              let uu____14482 =
                                let uu____14483 =
                                  let uu____14484 =
                                    let uu____14489 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14490 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14489, uu____14490)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14484  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14483
                                 in
                              quant xy uu____14482  in
                            (FStar_Parser_Const.op_GT, uu____14469)  in
                          let uu____14502 =
                            let uu____14520 =
                              let uu____14536 =
                                let uu____14549 =
                                  let uu____14550 =
                                    let uu____14551 =
                                      let uu____14556 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14557 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14556, uu____14557)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14551
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14550
                                   in
                                quant xy uu____14549  in
                              (FStar_Parser_Const.op_GTE, uu____14536)  in
                            let uu____14569 =
                              let uu____14587 =
                                let uu____14603 =
                                  let uu____14616 =
                                    let uu____14617 =
                                      let uu____14618 =
                                        let uu____14623 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14624 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14623, uu____14624)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14618
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14617
                                     in
                                  quant xy uu____14616  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14603)
                                 in
                              let uu____14636 =
                                let uu____14654 =
                                  let uu____14670 =
                                    let uu____14683 =
                                      let uu____14684 =
                                        let uu____14685 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14685
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14684
                                       in
                                    quant qx uu____14683  in
                                  (FStar_Parser_Const.op_Minus, uu____14670)
                                   in
                                let uu____14697 =
                                  let uu____14715 =
                                    let uu____14731 =
                                      let uu____14744 =
                                        let uu____14745 =
                                          let uu____14746 =
                                            let uu____14751 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14752 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14751, uu____14752)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14746
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14745
                                         in
                                      quant xy uu____14744  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14731)
                                     in
                                  let uu____14764 =
                                    let uu____14782 =
                                      let uu____14798 =
                                        let uu____14811 =
                                          let uu____14812 =
                                            let uu____14813 =
                                              let uu____14818 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14819 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14818, uu____14819)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14813
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14812
                                           in
                                        quant xy uu____14811  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14798)
                                       in
                                    let uu____14831 =
                                      let uu____14849 =
                                        let uu____14865 =
                                          let uu____14878 =
                                            let uu____14879 =
                                              let uu____14880 =
                                                let uu____14885 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14886 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14885, uu____14886)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14880
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14879
                                             in
                                          quant xy uu____14878  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14865)
                                         in
                                      let uu____14898 =
                                        let uu____14916 =
                                          let uu____14932 =
                                            let uu____14945 =
                                              let uu____14946 =
                                                let uu____14947 =
                                                  let uu____14952 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14953 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14952, uu____14953)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14947
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14946
                                               in
                                            quant xy uu____14945  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14932)
                                           in
                                        let uu____14965 =
                                          let uu____14983 =
                                            let uu____14999 =
                                              let uu____15012 =
                                                let uu____15013 =
                                                  let uu____15014 =
                                                    let uu____15019 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____15020 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____15019,
                                                      uu____15020)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15014
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____15013
                                                 in
                                              quant xy uu____15012  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14999)
                                             in
                                          let uu____15032 =
                                            let uu____15050 =
                                              let uu____15066 =
                                                let uu____15079 =
                                                  let uu____15080 =
                                                    let uu____15081 =
                                                      let uu____15086 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____15087 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____15086,
                                                        uu____15087)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____15081
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____15080
                                                   in
                                                quant xy uu____15079  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____15066)
                                               in
                                            let uu____15099 =
                                              let uu____15117 =
                                                let uu____15133 =
                                                  let uu____15146 =
                                                    let uu____15147 =
                                                      let uu____15148 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____15148
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____15147
                                                     in
                                                  quant qx uu____15146  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____15133)
                                                 in
                                              [uu____15117]  in
                                            uu____15050 :: uu____15099  in
                                          uu____14983 :: uu____15032  in
                                        uu____14916 :: uu____14965  in
                                      uu____14849 :: uu____14898  in
                                    uu____14782 :: uu____14831  in
                                  uu____14715 :: uu____14764  in
                                uu____14654 :: uu____14697  in
                              uu____14587 :: uu____14636  in
                            uu____14520 :: uu____14569  in
                          uu____14453 :: uu____14502  in
                        uu____14386 :: uu____14435  in
                      uu____14319 :: uu____14368  in
                    uu____14258 :: uu____14301  in
                  uu____14198 :: uu____14240  in
                let mk1 l v1 =
                  let uu____15419 =
                    let uu____15430 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15500  ->
                              match uu____15500 with
                              | (l',uu____15516) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____15430
                      (FStar_Option.map
                         (fun uu____15592  ->
                            match uu____15592 with | (uu____15615,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____15419 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15706  ->
                          match uu____15706 with
                          | (l',uu____15722) -> FStar_Ident.lid_equals l l'))
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
        let uu____15772 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15772 with
        | (xxsym,xx) ->
            let uu____15779 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15779 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15789 =
                   let uu____15796 =
                     let uu____15797 =
                       let uu____15808 =
                         let uu____15809 =
                           let uu____15814 =
                             let uu____15815 =
                               let uu____15820 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15820)  in
                             FStar_SMTEncoding_Util.mkEq uu____15815  in
                           (xx_has_type, uu____15814)  in
                         FStar_SMTEncoding_Util.mkImp uu____15809  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15808)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15797  in
                   let uu____15839 =
                     let uu____15840 =
                       let uu____15841 =
                         let uu____15842 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15842  in
                       Prims.strcat module_name uu____15841  in
                     varops.mk_unique uu____15840  in
                   (uu____15796, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15839)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15789)
  
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
    let uu____15890 =
      let uu____15891 =
        let uu____15898 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15898, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15891  in
    let uu____15899 =
      let uu____15902 =
        let uu____15903 =
          let uu____15910 =
            let uu____15911 =
              let uu____15922 =
                let uu____15923 =
                  let uu____15928 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15928)  in
                FStar_SMTEncoding_Util.mkImp uu____15923  in
              ([[typing_pred]], [xx], uu____15922)  in
            mkForall_fuel uu____15911  in
          (uu____15910, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15903  in
      [uu____15902]  in
    uu____15890 :: uu____15899  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15968 =
      let uu____15969 =
        let uu____15976 =
          let uu____15977 =
            let uu____15988 =
              let uu____15993 =
                let uu____15996 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15996]  in
              [uu____15993]  in
            let uu____16001 =
              let uu____16002 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16002 tt  in
            (uu____15988, [bb], uu____16001)  in
          FStar_SMTEncoding_Util.mkForall uu____15977  in
        (uu____15976, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15969  in
    let uu____16015 =
      let uu____16018 =
        let uu____16019 =
          let uu____16026 =
            let uu____16027 =
              let uu____16038 =
                let uu____16039 =
                  let uu____16044 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____16044)  in
                FStar_SMTEncoding_Util.mkImp uu____16039  in
              ([[typing_pred]], [xx], uu____16038)  in
            mkForall_fuel uu____16027  in
          (uu____16026, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16019  in
      [uu____16018]  in
    uu____15968 :: uu____16015  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____16092 =
        let uu____16093 =
          let uu____16100 =
            let uu____16103 =
              let uu____16106 =
                let uu____16109 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____16110 =
                  let uu____16113 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____16113]  in
                uu____16109 :: uu____16110  in
              tt :: uu____16106  in
            tt :: uu____16103  in
          ("Prims.Precedes", uu____16100)  in
        FStar_SMTEncoding_Util.mkApp uu____16093  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16092  in
    let precedes_y_x =
      let uu____16117 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16117  in
    let uu____16120 =
      let uu____16121 =
        let uu____16128 =
          let uu____16129 =
            let uu____16140 =
              let uu____16145 =
                let uu____16148 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____16148]  in
              [uu____16145]  in
            let uu____16153 =
              let uu____16154 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16154 tt  in
            (uu____16140, [bb], uu____16153)  in
          FStar_SMTEncoding_Util.mkForall uu____16129  in
        (uu____16128, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16121  in
    let uu____16167 =
      let uu____16170 =
        let uu____16171 =
          let uu____16178 =
            let uu____16179 =
              let uu____16190 =
                let uu____16191 =
                  let uu____16196 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____16196)  in
                FStar_SMTEncoding_Util.mkImp uu____16191  in
              ([[typing_pred]], [xx], uu____16190)  in
            mkForall_fuel uu____16179  in
          (uu____16178, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16171  in
      let uu____16213 =
        let uu____16216 =
          let uu____16217 =
            let uu____16224 =
              let uu____16225 =
                let uu____16236 =
                  let uu____16237 =
                    let uu____16242 =
                      let uu____16243 =
                        let uu____16246 =
                          let uu____16249 =
                            let uu____16252 =
                              let uu____16253 =
                                let uu____16258 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____16259 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____16258, uu____16259)  in
                              FStar_SMTEncoding_Util.mkGT uu____16253  in
                            let uu____16260 =
                              let uu____16263 =
                                let uu____16264 =
                                  let uu____16269 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____16270 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____16269, uu____16270)  in
                                FStar_SMTEncoding_Util.mkGTE uu____16264  in
                              let uu____16271 =
                                let uu____16274 =
                                  let uu____16275 =
                                    let uu____16280 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____16281 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____16280, uu____16281)  in
                                  FStar_SMTEncoding_Util.mkLT uu____16275  in
                                [uu____16274]  in
                              uu____16263 :: uu____16271  in
                            uu____16252 :: uu____16260  in
                          typing_pred_y :: uu____16249  in
                        typing_pred :: uu____16246  in
                      FStar_SMTEncoding_Util.mk_and_l uu____16243  in
                    (uu____16242, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____16237  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____16236)
                 in
              mkForall_fuel uu____16225  in
            (uu____16224,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____16217  in
        [uu____16216]  in
      uu____16170 :: uu____16213  in
    uu____16120 :: uu____16167  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16325 =
      let uu____16326 =
        let uu____16333 =
          let uu____16334 =
            let uu____16345 =
              let uu____16350 =
                let uu____16353 = FStar_SMTEncoding_Term.boxString b  in
                [uu____16353]  in
              [uu____16350]  in
            let uu____16358 =
              let uu____16359 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16359 tt  in
            (uu____16345, [bb], uu____16358)  in
          FStar_SMTEncoding_Util.mkForall uu____16334  in
        (uu____16333, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16326  in
    let uu____16372 =
      let uu____16375 =
        let uu____16376 =
          let uu____16383 =
            let uu____16384 =
              let uu____16395 =
                let uu____16396 =
                  let uu____16401 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____16401)  in
                FStar_SMTEncoding_Util.mkImp uu____16396  in
              ([[typing_pred]], [xx], uu____16395)  in
            mkForall_fuel uu____16384  in
          (uu____16383, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16376  in
      [uu____16375]  in
    uu____16325 :: uu____16372  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____16456 =
      let uu____16457 =
        let uu____16464 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____16464, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16457  in
    [uu____16456]  in
  let mk_and_interp env conj uu____16480 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16505 =
      let uu____16506 =
        let uu____16513 =
          let uu____16514 =
            let uu____16525 =
              let uu____16526 =
                let uu____16531 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16531, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16526  in
            ([[l_and_a_b]], [aa; bb], uu____16525)  in
          FStar_SMTEncoding_Util.mkForall uu____16514  in
        (uu____16513, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16506  in
    [uu____16505]  in
  let mk_or_interp env disj uu____16567 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16592 =
      let uu____16593 =
        let uu____16600 =
          let uu____16601 =
            let uu____16612 =
              let uu____16613 =
                let uu____16618 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16618, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16613  in
            ([[l_or_a_b]], [aa; bb], uu____16612)  in
          FStar_SMTEncoding_Util.mkForall uu____16601  in
        (uu____16600, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16593  in
    [uu____16592]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16679 =
      let uu____16680 =
        let uu____16687 =
          let uu____16688 =
            let uu____16699 =
              let uu____16700 =
                let uu____16705 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16705, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16700  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16699)  in
          FStar_SMTEncoding_Util.mkForall uu____16688  in
        (uu____16687, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16680  in
    [uu____16679]  in
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
    let uu____16776 =
      let uu____16777 =
        let uu____16784 =
          let uu____16785 =
            let uu____16796 =
              let uu____16797 =
                let uu____16802 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16802, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16797  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16796)  in
          FStar_SMTEncoding_Util.mkForall uu____16785  in
        (uu____16784, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16777  in
    [uu____16776]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16871 =
      let uu____16872 =
        let uu____16879 =
          let uu____16880 =
            let uu____16891 =
              let uu____16892 =
                let uu____16897 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16897, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16892  in
            ([[l_imp_a_b]], [aa; bb], uu____16891)  in
          FStar_SMTEncoding_Util.mkForall uu____16880  in
        (uu____16879, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16872  in
    [uu____16871]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16958 =
      let uu____16959 =
        let uu____16966 =
          let uu____16967 =
            let uu____16978 =
              let uu____16979 =
                let uu____16984 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16984, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16979  in
            ([[l_iff_a_b]], [aa; bb], uu____16978)  in
          FStar_SMTEncoding_Util.mkForall uu____16967  in
        (uu____16966, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16959  in
    [uu____16958]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____17034 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____17034  in
    let uu____17037 =
      let uu____17038 =
        let uu____17045 =
          let uu____17046 =
            let uu____17057 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____17057)  in
          FStar_SMTEncoding_Util.mkForall uu____17046  in
        (uu____17045, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17038  in
    [uu____17037]  in
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
      let uu____17115 =
        let uu____17122 =
          let uu____17125 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17125]  in
        ("Valid", uu____17122)  in
      FStar_SMTEncoding_Util.mkApp uu____17115  in
    let uu____17128 =
      let uu____17129 =
        let uu____17136 =
          let uu____17137 =
            let uu____17148 =
              let uu____17149 =
                let uu____17154 =
                  let uu____17155 =
                    let uu____17166 =
                      let uu____17171 =
                        let uu____17174 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17174]  in
                      [uu____17171]  in
                    let uu____17179 =
                      let uu____17180 =
                        let uu____17185 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17185, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17180  in
                    (uu____17166, [xx1], uu____17179)  in
                  FStar_SMTEncoding_Util.mkForall uu____17155  in
                (uu____17154, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17149  in
            ([[l_forall_a_b]], [aa; bb], uu____17148)  in
          FStar_SMTEncoding_Util.mkForall uu____17137  in
        (uu____17136, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17129  in
    [uu____17128]  in
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
      let uu____17259 =
        let uu____17266 =
          let uu____17269 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17269]  in
        ("Valid", uu____17266)  in
      FStar_SMTEncoding_Util.mkApp uu____17259  in
    let uu____17272 =
      let uu____17273 =
        let uu____17280 =
          let uu____17281 =
            let uu____17292 =
              let uu____17293 =
                let uu____17298 =
                  let uu____17299 =
                    let uu____17310 =
                      let uu____17315 =
                        let uu____17318 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17318]  in
                      [uu____17315]  in
                    let uu____17323 =
                      let uu____17324 =
                        let uu____17329 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17329, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17324  in
                    (uu____17310, [xx1], uu____17323)  in
                  FStar_SMTEncoding_Util.mkExists uu____17299  in
                (uu____17298, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17293  in
            ([[l_exists_a_b]], [aa; bb], uu____17292)  in
          FStar_SMTEncoding_Util.mkForall uu____17281  in
        (uu____17280, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17273  in
    [uu____17272]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____17381 =
      let uu____17382 =
        let uu____17389 =
          let uu____17390 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____17390 range_ty  in
        let uu____17391 = varops.mk_unique "typing_range_const"  in
        (uu____17389, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____17391)
         in
      FStar_SMTEncoding_Util.mkAssume uu____17382  in
    [uu____17381]  in
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
        let uu____17429 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17429 x1 t  in
      let uu____17430 =
        let uu____17441 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____17441)  in
      FStar_SMTEncoding_Util.mkForall uu____17430  in
    let uu____17458 =
      let uu____17459 =
        let uu____17466 =
          let uu____17467 =
            let uu____17478 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____17478)  in
          FStar_SMTEncoding_Util.mkForall uu____17467  in
        (uu____17466,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17459  in
    [uu____17458]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17526 =
      let uu____17527 =
        let uu____17534 =
          let uu____17535 =
            let uu____17550 =
              let uu____17551 =
                let uu____17556 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17557 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17556, uu____17557)  in
              FStar_SMTEncoding_Util.mkAnd uu____17551  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17550)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17535  in
        (uu____17534,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17527  in
    [uu____17526]  in
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
          let uu____18085 =
            FStar_Util.find_opt
              (fun uu____18121  ->
                 match uu____18121 with
                 | (l,uu____18135) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____18085 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____18175,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____18232 = encode_function_type_as_formula t env  in
        match uu____18232 with
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
              let uu____18290 =
                ((let uu____18293 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____18293) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____18290
              then
                let arg_sorts =
                  let uu____18303 =
                    let uu____18304 = FStar_Syntax_Subst.compress t_norm  in
                    uu____18304.FStar_Syntax_Syntax.n  in
                  match uu____18303 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____18310) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____18340  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____18345 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____18347 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____18347 with
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
                (let uu____18376 = prims.is lid  in
                 if uu____18376
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____18384 = prims.mk lid vname  in
                   match uu____18384 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____18411 =
                      let uu____18424 = curried_arrow_formals_comp t_norm  in
                      match uu____18424 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____18446 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____18446
                            then
                              let uu____18449 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___122_18452 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___122_18452.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___122_18452.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___122_18452.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___122_18452.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___122_18452.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___122_18452.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___122_18452.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___122_18452.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___122_18452.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___122_18452.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___122_18452.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___122_18452.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___122_18452.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___122_18452.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___122_18452.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___122_18452.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___122_18452.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___122_18452.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___122_18452.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___122_18452.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___122_18452.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___122_18452.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___122_18452.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___122_18452.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___122_18452.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___122_18452.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___122_18452.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___122_18452.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___122_18452.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___122_18452.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___122_18452.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___122_18452.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___122_18452.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___122_18452.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___122_18452.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___122_18452.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___122_18452.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____18449
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____18466 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____18466)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____18411 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____18522 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____18522 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____18547 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___96_18597  ->
                                       match uu___96_18597 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____18601 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18601 with
                                            | (uu____18622,(xxsym,uu____18624))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____18642 =
                                                  let uu____18643 =
                                                    let uu____18650 =
                                                      let uu____18651 =
                                                        let uu____18662 =
                                                          let uu____18663 =
                                                            let uu____18668 =
                                                              let uu____18669
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____18669
                                                               in
                                                            (vapp,
                                                              uu____18668)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____18663
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18662)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18651
                                                       in
                                                    (uu____18650,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18643
                                                   in
                                                [uu____18642])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____18680 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18680 with
                                            | (uu____18701,(xxsym,uu____18703))
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
                                                let uu____18726 =
                                                  let uu____18727 =
                                                    let uu____18734 =
                                                      let uu____18735 =
                                                        let uu____18746 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18746)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18735
                                                       in
                                                    (uu____18734,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18727
                                                   in
                                                [uu____18726])
                                       | uu____18755 -> []))
                                in
                             let uu____18756 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____18756 with
                              | (vars,guards,env',decls1,uu____18783) ->
                                  let uu____18796 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18809 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18809, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18813 =
                                          encode_formula p env'  in
                                        (match uu____18813 with
                                         | (g,ds) ->
                                             let uu____18826 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____18826,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18796 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____18843 =
                                           let uu____18850 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____18850)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____18843
                                          in
                                       let uu____18855 =
                                         let vname_decl =
                                           let uu____18863 =
                                             let uu____18874 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____18890  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____18874,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____18863
                                            in
                                         let uu____18897 =
                                           let env2 =
                                             let uu___123_18903 = env1  in
                                             {
                                               bindings =
                                                 (uu___123_18903.bindings);
                                               depth = (uu___123_18903.depth);
                                               tcenv = (uu___123_18903.tcenv);
                                               warn = (uu___123_18903.warn);
                                               cache = (uu___123_18903.cache);
                                               nolabels =
                                                 (uu___123_18903.nolabels);
                                               use_zfuel_name =
                                                 (uu___123_18903.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___123_18903.current_module_name)
                                             }  in
                                           let uu____18904 =
                                             let uu____18905 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____18905
                                              in
                                           if uu____18904
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____18897 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____18920::uu____18921 ->
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
                                                     let uu____18961 =
                                                       let uu____18972 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____18972)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____18961
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____18991 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____18992 =
                                               match formals with
                                               | [] ->
                                                   let uu____19009 =
                                                     let uu____19010 =
                                                       let uu____19013 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____19013
                                                        in
                                                     replace_free_var env1
                                                       lid arity vname
                                                       uu____19010
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____19009)
                                               | uu____19022 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____19027 =
                                                       let uu____19034 =
                                                         let uu____19035 =
                                                           let uu____19046 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____19046)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____19035
                                                          in
                                                       (uu____19034,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____19027
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____18992 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____18855 with
                                        | (decls2,env2) ->
                                            let uu____19085 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____19093 =
                                                encode_term res_t1 env'  in
                                              match uu____19093 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____19106 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____19106, decls)
                                               in
                                            (match uu____19085 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____19117 =
                                                     let uu____19124 =
                                                       let uu____19125 =
                                                         let uu____19136 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____19136)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____19125
                                                        in
                                                     (uu____19124,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____19117
                                                    in
                                                 let freshness =
                                                   let uu____19148 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____19148
                                                   then
                                                     let uu____19153 =
                                                       let uu____19154 =
                                                         let uu____19165 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____19180 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____19165,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____19180)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____19154
                                                        in
                                                     let uu____19183 =
                                                       let uu____19186 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____19186]  in
                                                     uu____19153 ::
                                                       uu____19183
                                                   else []  in
                                                 let g =
                                                   let uu____19191 =
                                                     let uu____19194 =
                                                       let uu____19197 =
                                                         let uu____19200 =
                                                           let uu____19203 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____19203
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____19200
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____19197
                                                        in
                                                     FStar_List.append decls2
                                                       uu____19194
                                                      in
                                                   FStar_List.append decls11
                                                     uu____19191
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
          let uu____19244 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19244 with
          | FStar_Pervasives_Native.None  ->
              let uu____19255 = encode_free_var false env x t t_norm []  in
              (match uu____19255 with
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
            let uu____19322 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____19322 with
            | (decls,env1) ->
                let uu____19341 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____19341
                then
                  let uu____19348 =
                    let uu____19351 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____19351  in
                  (uu____19348, env1)
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
             (fun uu____19409  ->
                fun lb  ->
                  match uu____19409 with
                  | (decls,env1) ->
                      let uu____19429 =
                        let uu____19436 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____19436
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____19429 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____19459 = FStar_Syntax_Util.head_and_args t  in
    match uu____19459 with
    | (hd1,args) ->
        let uu____19490 =
          let uu____19491 = FStar_Syntax_Util.un_uinst hd1  in
          uu____19491.FStar_Syntax_Syntax.n  in
        (match uu____19490 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____19495,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____19514 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____19542  ->
      fun quals  ->
        match uu____19542 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____19634 = FStar_Util.first_N nbinders formals  in
              match uu____19634 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19715  ->
                         fun uu____19716  ->
                           match (uu____19715, uu____19716) with
                           | ((formal,uu____19734),(binder,uu____19736)) ->
                               let uu____19745 =
                                 let uu____19752 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19752)  in
                               FStar_Syntax_Syntax.NT uu____19745) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19764 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19795  ->
                              match uu____19795 with
                              | (x,i) ->
                                  let uu____19806 =
                                    let uu___124_19807 = x  in
                                    let uu____19808 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___124_19807.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___124_19807.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19808
                                    }  in
                                  (uu____19806, i)))
                       in
                    FStar_All.pipe_right uu____19764
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19826 =
                      let uu____19831 = FStar_Syntax_Subst.compress body  in
                      let uu____19832 =
                        let uu____19833 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____19833
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____19831
                        uu____19832
                       in
                    uu____19826 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____19912 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____19912
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___125_19917 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___125_19917.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___125_19917.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___125_19917.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___125_19917.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___125_19917.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___125_19917.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___125_19917.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___125_19917.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___125_19917.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___125_19917.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___125_19917.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___125_19917.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___125_19917.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___125_19917.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___125_19917.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___125_19917.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___125_19917.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___125_19917.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___125_19917.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___125_19917.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___125_19917.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___125_19917.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___125_19917.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___125_19917.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___125_19917.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___125_19917.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___125_19917.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___125_19917.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___125_19917.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___125_19917.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___125_19917.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___125_19917.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___125_19917.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___125_19917.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___125_19917.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___125_19917.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___125_19917.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____19958 = FStar_Syntax_Util.abs_formals e  in
                match uu____19958 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____20030::uu____20031 ->
                         let uu____20046 =
                           let uu____20047 =
                             let uu____20050 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____20050
                              in
                           uu____20047.FStar_Syntax_Syntax.n  in
                         (match uu____20046 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____20099 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____20099 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____20147 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____20147
                                   then
                                     let uu____20186 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____20186 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____20284  ->
                                                   fun uu____20285  ->
                                                     match (uu____20284,
                                                             uu____20285)
                                                     with
                                                     | ((x,uu____20303),
                                                        (b,uu____20305)) ->
                                                         let uu____20314 =
                                                           let uu____20321 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____20321)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____20314)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____20329 =
                                            let uu____20354 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____20354)
                                             in
                                          (uu____20329, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____20436 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____20436 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____20537) ->
                              let uu____20542 =
                                let uu____20567 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____20567  in
                              (uu____20542, true)
                          | uu____20644 when Prims.op_Negation norm1 ->
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
                          | uu____20646 ->
                              let uu____20647 =
                                let uu____20648 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____20649 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____20648
                                  uu____20649
                                 in
                              failwith uu____20647)
                     | uu____20678 ->
                         let rec aux' t_norm2 =
                           let uu____20711 =
                             let uu____20712 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____20712.FStar_Syntax_Syntax.n  in
                           match uu____20711 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____20759 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____20759 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____20795 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____20795 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20885)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20890 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20950 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20950
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20962 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____21025  ->
                            fun lb  ->
                              match uu____21025 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____21080 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____21080
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____21083 =
                                      let uu____21092 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____21092
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____21083 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____20962 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____21217 =
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
                        | uu____21223 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____21231 = mk_fv ()  in
                                   mk_Apply uu____21231 vars)
                            else
                              (let uu____21233 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____21233)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____21293;
                             FStar_Syntax_Syntax.lbeff = uu____21294;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____21296;
                             FStar_Syntax_Syntax.lbpos = uu____21297;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____21321 =
                              let uu____21328 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____21328 with
                              | (tcenv',uu____21344,e_t) ->
                                  let uu____21350 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____21361 -> failwith "Impossible"
                                     in
                                  (match uu____21350 with
                                   | (e1,t_norm1) ->
                                       ((let uu___128_21377 = env2  in
                                         {
                                           bindings =
                                             (uu___128_21377.bindings);
                                           depth = (uu___128_21377.depth);
                                           tcenv = tcenv';
                                           warn = (uu___128_21377.warn);
                                           cache = (uu___128_21377.cache);
                                           nolabels =
                                             (uu___128_21377.nolabels);
                                           use_zfuel_name =
                                             (uu___128_21377.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___128_21377.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___128_21377.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____21321 with
                             | (env',e1,t_norm1) ->
                                 let uu____21387 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____21387 with
                                  | ((binders,body,uu____21408,t_body),curry)
                                      ->
                                      ((let uu____21420 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____21420
                                        then
                                          let uu____21421 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____21422 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____21421 uu____21422
                                        else ());
                                       (let uu____21424 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____21424 with
                                        | (vars,guards,env'1,binder_decls,uu____21451)
                                            ->
                                            let body1 =
                                              let uu____21465 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____21465
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
                                              let uu____21486 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____21486 curry fvb
                                                vars
                                               in
                                            let uu____21487 =
                                              let uu____21496 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____21496
                                              then
                                                let uu____21507 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____21508 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____21507, uu____21508)
                                              else
                                                (let uu____21518 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____21518))
                                               in
                                            (match uu____21487 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____21541 =
                                                     let uu____21548 =
                                                       let uu____21549 =
                                                         let uu____21560 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____21560)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____21549
                                                        in
                                                     let uu____21569 =
                                                       let uu____21570 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21570
                                                        in
                                                     (uu____21548,
                                                       uu____21569,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____21541
                                                    in
                                                 let uu____21571 =
                                                   let uu____21574 =
                                                     let uu____21577 =
                                                       let uu____21580 =
                                                         let uu____21583 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____21583
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____21580
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____21577
                                                      in
                                                   FStar_List.append decls1
                                                     uu____21574
                                                    in
                                                 (uu____21571, env2))))))
                        | uu____21588 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____21651 = varops.fresh "fuel"  in
                          (uu____21651, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21654 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____21701  ->
                                  fun fvb  ->
                                    match uu____21701 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____21747 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21747  in
                                        let gtok =
                                          let uu____21749 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21749  in
                                        let env4 =
                                          let uu____21751 =
                                            let uu____21754 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____21754
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____21751
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____21654 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21860 t_norm
                              uu____21862 =
                              match (uu____21860, uu____21862) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____21890;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____21891;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____21893;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____21894;_})
                                  ->
                                  let uu____21915 =
                                    let uu____21922 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21922 with
                                    | (tcenv',uu____21938,e_t) ->
                                        let uu____21944 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21955 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21944 with
                                         | (e1,t_norm1) ->
                                             ((let uu___129_21971 = env3  in
                                               {
                                                 bindings =
                                                   (uu___129_21971.bindings);
                                                 depth =
                                                   (uu___129_21971.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___129_21971.warn);
                                                 cache =
                                                   (uu___129_21971.cache);
                                                 nolabels =
                                                   (uu___129_21971.nolabels);
                                                 use_zfuel_name =
                                                   (uu___129_21971.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___129_21971.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___129_21971.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21915 with
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
                                                     let uu____22108 =
                                                       let uu____22115 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____22115)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22108
                                                      in
                                                   let gsapp =
                                                     let uu____22121 =
                                                       let uu____22128 =
                                                         let uu____22131 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____22131 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22128)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22121
                                                      in
                                                   let gmax =
                                                     let uu____22137 =
                                                       let uu____22144 =
                                                         let uu____22147 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____22147 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22144)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22137
                                                      in
                                                   let body1 =
                                                     let uu____22153 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____22153
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____22155 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____22155 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____22173 =
                                                            let uu____22180 =
                                                              let uu____22181
                                                                =
                                                                let uu____22196
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
                                                                  uu____22196)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____22181
                                                               in
                                                            let uu____22207 =
                                                              let uu____22208
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____22208
                                                               in
                                                            (uu____22180,
                                                              uu____22207,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22173
                                                           in
                                                        let eqn_f =
                                                          let uu____22210 =
                                                            let uu____22217 =
                                                              let uu____22218
                                                                =
                                                                let uu____22229
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____22229)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22218
                                                               in
                                                            (uu____22217,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22210
                                                           in
                                                        let eqn_g' =
                                                          let uu____22239 =
                                                            let uu____22246 =
                                                              let uu____22247
                                                                =
                                                                let uu____22258
                                                                  =
                                                                  let uu____22259
                                                                    =
                                                                    let uu____22264
                                                                    =
                                                                    let uu____22265
                                                                    =
                                                                    let uu____22272
                                                                    =
                                                                    let uu____22275
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____22275
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____22272)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____22265
                                                                     in
                                                                    (gsapp,
                                                                    uu____22264)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____22259
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____22258)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22247
                                                               in
                                                            (uu____22246,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22239
                                                           in
                                                        let uu____22286 =
                                                          let uu____22295 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____22295
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____22324)
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
                                                                  let uu____22345
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____22345
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____22346
                                                                  =
                                                                  let uu____22353
                                                                    =
                                                                    let uu____22354
                                                                    =
                                                                    let uu____22365
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22365)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22354
                                                                     in
                                                                  (uu____22353,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____22346
                                                                 in
                                                              let uu____22374
                                                                =
                                                                let uu____22381
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____22381
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____22394
                                                                    =
                                                                    let uu____22397
                                                                    =
                                                                    let uu____22398
                                                                    =
                                                                    let uu____22405
                                                                    =
                                                                    let uu____22406
                                                                    =
                                                                    let uu____22417
                                                                    =
                                                                    let uu____22418
                                                                    =
                                                                    let uu____22423
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____22423,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____22418
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22417)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22406
                                                                     in
                                                                    (uu____22405,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____22398
                                                                     in
                                                                    [uu____22397]
                                                                     in
                                                                    (d3,
                                                                    uu____22394)
                                                                 in
                                                              (match uu____22374
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
                                                        (match uu____22286
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
                            let uu____22476 =
                              let uu____22489 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22546  ->
                                   fun uu____22547  ->
                                     match (uu____22546, uu____22547) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22662 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22662 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22489
                               in
                            (match uu____22476 with
                             | (decls2,eqns,env01) ->
                                 let uu____22735 =
                                   let isDeclFun uu___97_22749 =
                                     match uu___97_22749 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22750 -> true
                                     | uu____22761 -> false  in
                                   let uu____22762 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22762
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22735 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22802 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___98_22806  ->
                                 match uu___98_22806 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22807 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22813 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22813)))
                         in
                      if uu____22802
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
                   let uu____22865 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22865
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
        let uu____22926 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22926 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22930 = encode_sigelt' env se  in
      match uu____22930 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22942 =
                  let uu____22943 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22943  in
                [uu____22942]
            | uu____22944 ->
                let uu____22945 =
                  let uu____22948 =
                    let uu____22949 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22949  in
                  uu____22948 :: g  in
                let uu____22950 =
                  let uu____22953 =
                    let uu____22954 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22954  in
                  [uu____22953]  in
                FStar_List.append uu____22945 uu____22950
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
        let uu____22967 =
          let uu____22968 = FStar_Syntax_Subst.compress t  in
          uu____22968.FStar_Syntax_Syntax.n  in
        match uu____22967 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22972)) -> s = "opaque_to_smt"
        | uu____22973 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22980 =
          let uu____22981 = FStar_Syntax_Subst.compress t  in
          uu____22981.FStar_Syntax_Syntax.n  in
        match uu____22980 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22985)) -> s = "uninterpreted_by_smt"
        | uu____22986 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22991 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____22996 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____23007 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____23008 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____23009 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____23022 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23024 =
            let uu____23025 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____23025 Prims.op_Negation  in
          if uu____23024
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____23051 ->
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
               let uu____23081 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____23081 with
               | (formals,uu____23099) ->
                   let arity = FStar_List.length formals  in
                   let uu____23117 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____23117 with
                    | (aname,atok,env2) ->
                        let uu____23137 =
                          let uu____23142 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____23142 env2  in
                        (match uu____23137 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____23154 =
                                 let uu____23155 =
                                   let uu____23166 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____23182  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____23166,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____23155
                                  in
                               [uu____23154;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____23191 =
                               let aux uu____23247 uu____23248 =
                                 match (uu____23247, uu____23248) with
                                 | ((bv,uu____23300),(env3,acc_sorts,acc)) ->
                                     let uu____23338 = gen_term_var env3 bv
                                        in
                                     (match uu____23338 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____23191 with
                              | (uu____23410,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____23433 =
                                      let uu____23440 =
                                        let uu____23441 =
                                          let uu____23452 =
                                            let uu____23453 =
                                              let uu____23458 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____23458)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23453
                                             in
                                          ([[app]], xs_sorts, uu____23452)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23441
                                         in
                                      (uu____23440,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23433
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23470 =
                                      let uu____23477 =
                                        let uu____23478 =
                                          let uu____23489 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23489)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23478
                                         in
                                      (uu____23477,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23470
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23500 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23500 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23526,uu____23527)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23528 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____23528 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23543,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23549 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___99_23553  ->
                      match uu___99_23553 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23554 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23559 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23560 -> false))
               in
            Prims.op_Negation uu____23549  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23567 =
               let uu____23574 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23574 env fv t quals  in
             match uu____23567 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23589 =
                   let uu____23590 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23590  in
                 (uu____23589, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23596 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23596 with
           | (uu____23605,f1) ->
               let uu____23607 = encode_formula f1 env  in
               (match uu____23607 with
                | (f2,decls) ->
                    let g =
                      let uu____23621 =
                        let uu____23622 =
                          let uu____23629 =
                            let uu____23630 =
                              let uu____23631 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23631
                               in
                            FStar_Pervasives_Native.Some uu____23630  in
                          let uu____23632 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23629, uu____23632)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23622  in
                      [uu____23621]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23634) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23646 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23668 =
                       let uu____23671 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23671.FStar_Syntax_Syntax.fv_name  in
                     uu____23668.FStar_Syntax_Syntax.v  in
                   let uu____23672 =
                     let uu____23673 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23673  in
                   if uu____23672
                   then
                     let val_decl =
                       let uu___132_23703 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___132_23703.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___132_23703.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___132_23703.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23704 = encode_sigelt' env1 val_decl  in
                     match uu____23704 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23646 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23738,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23740;
                          FStar_Syntax_Syntax.lbtyp = uu____23741;
                          FStar_Syntax_Syntax.lbeff = uu____23742;
                          FStar_Syntax_Syntax.lbdef = uu____23743;
                          FStar_Syntax_Syntax.lbattrs = uu____23744;
                          FStar_Syntax_Syntax.lbpos = uu____23745;_}::[]),uu____23746)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23763 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____23763 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23792 =
                   let uu____23795 =
                     let uu____23796 =
                       let uu____23803 =
                         let uu____23804 =
                           let uu____23815 =
                             let uu____23816 =
                               let uu____23821 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23821)  in
                             FStar_SMTEncoding_Util.mkEq uu____23816  in
                           ([[b2t_x]], [xx], uu____23815)  in
                         FStar_SMTEncoding_Util.mkForall uu____23804  in
                       (uu____23803,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23796  in
                   [uu____23795]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23792
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23842,uu____23843) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_23852  ->
                  match uu___100_23852 with
                  | FStar_Syntax_Syntax.Discriminator uu____23853 -> true
                  | uu____23854 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23855,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23866 =
                     let uu____23867 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23867.FStar_Ident.idText  in
                   uu____23866 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___101_23871  ->
                     match uu___101_23871 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23872 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23874) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___102_23885  ->
                  match uu___102_23885 with
                  | FStar_Syntax_Syntax.Projector uu____23886 -> true
                  | uu____23891 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23894 = try_lookup_free_var env l  in
          (match uu____23894 with
           | FStar_Pervasives_Native.Some uu____23901 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___133_23903 = se  in
                 let uu____23904 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____23904;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_23903.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_23903.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___133_23903.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23907) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23919) ->
          let uu____23928 = encode_sigelts env ses  in
          (match uu____23928 with
           | (g,env1) ->
               let uu____23945 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___103_23968  ->
                         match uu___103_23968 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23969;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23970;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23971;_}
                             -> false
                         | uu____23974 -> true))
                  in
               (match uu____23945 with
                | (g',inversions) ->
                    let uu____23989 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___104_24010  ->
                              match uu___104_24010 with
                              | FStar_SMTEncoding_Term.DeclFun uu____24011 ->
                                  true
                              | uu____24022 -> false))
                       in
                    (match uu____23989 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____24038,tps,k,uu____24041,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___105_24058  ->
                    match uu___105_24058 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____24059 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____24070 = c  in
              match uu____24070 with
              | (name,args,uu____24075,uu____24076,uu____24077) ->
                  let uu____24082 =
                    let uu____24083 =
                      let uu____24094 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____24117  ->
                                match uu____24117 with
                                | (uu____24124,sort,uu____24126) -> sort))
                         in
                      (name, uu____24094, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____24083  in
                  [uu____24082]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____24155 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____24161 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____24161 FStar_Option.isNone))
               in
            if uu____24155
            then []
            else
              (let uu____24193 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____24193 with
               | (xxsym,xx) ->
                   let uu____24202 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____24241  ->
                             fun l  ->
                               match uu____24241 with
                               | (out,decls) ->
                                   let uu____24261 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____24261 with
                                    | (uu____24272,data_t) ->
                                        let uu____24274 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____24274 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____24312 =
                                                 let uu____24313 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____24313.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____24312 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____24316,indices) ->
                                                   indices
                                               | uu____24338 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24362  ->
                                                         match uu____24362
                                                         with
                                                         | (x,uu____24368) ->
                                                             let uu____24369
                                                               =
                                                               let uu____24370
                                                                 =
                                                                 let uu____24377
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____24377,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24370
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____24369)
                                                    env)
                                                in
                                             let uu____24380 =
                                               encode_args indices env1  in
                                             (match uu____24380 with
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
                                                      let uu____24406 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____24422
                                                                 =
                                                                 let uu____24427
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____24427,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____24422)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____24406
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____24430 =
                                                      let uu____24431 =
                                                        let uu____24436 =
                                                          let uu____24437 =
                                                            let uu____24442 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____24442,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____24437
                                                           in
                                                        (out, uu____24436)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____24431
                                                       in
                                                    (uu____24430,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____24202 with
                    | (data_ax,decls) ->
                        let uu____24455 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____24455 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24466 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24466 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____24470 =
                                 let uu____24477 =
                                   let uu____24478 =
                                     let uu____24489 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24498 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24489,
                                       uu____24498)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24478
                                    in
                                 let uu____24507 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____24477,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24507)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____24470
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24508 =
            let uu____24521 =
              let uu____24522 = FStar_Syntax_Subst.compress k  in
              uu____24522.FStar_Syntax_Syntax.n  in
            match uu____24521 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24567 -> (tps, k)  in
          (match uu____24508 with
           | (formals,res) ->
               let uu____24590 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24590 with
                | (formals1,res1) ->
                    let uu____24601 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24601 with
                     | (vars,guards,env',binder_decls,uu____24626) ->
                         let arity = FStar_List.length vars  in
                         let uu____24640 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____24640 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24663 =
                                  let uu____24670 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24670)  in
                                FStar_SMTEncoding_Util.mkApp uu____24663  in
                              let uu____24675 =
                                let tname_decl =
                                  let uu____24685 =
                                    let uu____24686 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24710  ->
                                              match uu____24710 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24723 = varops.next_id ()  in
                                    (tname, uu____24686,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24723, false)
                                     in
                                  constructor_or_logic_type_decl uu____24685
                                   in
                                let uu____24726 =
                                  match vars with
                                  | [] ->
                                      let uu____24739 =
                                        let uu____24740 =
                                          let uu____24743 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____24743
                                           in
                                        replace_free_var env1 t arity tname
                                          uu____24740
                                         in
                                      ([], uu____24739)
                                  | uu____24754 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24761 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24761
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24775 =
                                          let uu____24782 =
                                            let uu____24783 =
                                              let uu____24798 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24798)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24783
                                             in
                                          (uu____24782,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24775
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24726 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24675 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24834 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24834 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24852 =
                                               let uu____24853 =
                                                 let uu____24860 =
                                                   let uu____24861 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24861
                                                    in
                                                 (uu____24860,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24853
                                                in
                                             [uu____24852]
                                           else []  in
                                         let uu____24863 =
                                           let uu____24866 =
                                             let uu____24869 =
                                               let uu____24870 =
                                                 let uu____24877 =
                                                   let uu____24878 =
                                                     let uu____24889 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24889)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24878
                                                    in
                                                 (uu____24877,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24870
                                                in
                                             [uu____24869]  in
                                           FStar_List.append karr uu____24866
                                            in
                                         FStar_List.append decls1 uu____24863
                                      in
                                   let aux =
                                     let uu____24901 =
                                       let uu____24904 =
                                         inversion_axioms tapp vars  in
                                       let uu____24907 =
                                         let uu____24910 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24910]  in
                                       FStar_List.append uu____24904
                                         uu____24907
                                        in
                                     FStar_List.append kindingAx uu____24901
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24915,uu____24916,uu____24917,uu____24918,uu____24919)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24925,t,uu____24927,n_tps,uu____24929) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24937 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____24937 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____24977 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____24977 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____24998 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24998 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____25012 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____25012 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____25070 =
                                            mk_term_projector_name d x  in
                                          (uu____25070,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____25074 =
                                  let uu____25075 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____25075, true)
                                   in
                                FStar_All.pipe_right uu____25074
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
                              let uu____25088 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____25088 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____25100::uu____25101 ->
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
                                         let uu____25128 =
                                           let uu____25139 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____25139)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____25128
                                     | uu____25158 -> tok_typing  in
                                   let uu____25161 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____25161 with
                                    | (vars',guards',env'',decls_formals,uu____25186)
                                        ->
                                        let uu____25199 =
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
                                        (match uu____25199 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25226 ->
                                                   let uu____25233 =
                                                     let uu____25234 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25234
                                                      in
                                                   [uu____25233]
                                                in
                                             let encode_elim uu____25248 =
                                               let uu____25249 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____25249 with
                                               | (head1,args) ->
                                                   let uu____25288 =
                                                     let uu____25289 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____25289.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____25288 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25301;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25302;_},uu____25303)
                                                        ->
                                                        let uu____25308 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25308
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25323
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25323
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
                                                                    uu____25374
                                                                    ->
                                                                    let uu____25375
                                                                    =
                                                                    let uu____25380
                                                                    =
                                                                    let uu____25381
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25381
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25380)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25375
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25397
                                                                    =
                                                                    let uu____25398
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25398
                                                                     in
                                                                    if
                                                                    uu____25397
                                                                    then
                                                                    let uu____25411
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25411]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25413
                                                                    =
                                                                    let uu____25426
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25476
                                                                     ->
                                                                    fun
                                                                    uu____25477
                                                                     ->
                                                                    match 
                                                                    (uu____25476,
                                                                    uu____25477)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25572
                                                                    =
                                                                    let uu____25579
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25579
                                                                     in
                                                                    (match uu____25572
                                                                    with
                                                                    | 
                                                                    (uu____25592,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25600
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25600
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25602
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25602
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
                                                                    uu____25426
                                                                     in
                                                                  (match uu____25413
                                                                   with
                                                                   | 
                                                                   (uu____25619,arg_vars,elim_eqns_or_guards,uu____25622)
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
                                                                    let uu____25646
                                                                    =
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25666
                                                                    =
                                                                    let uu____25667
                                                                    =
                                                                    let uu____25672
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25672)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25667
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25665,
                                                                    uu____25666)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25654
                                                                     in
                                                                    (uu____25653,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25646
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____25682
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____25682
                                                                    then
                                                                    let x =
                                                                    let uu____25688
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25688,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25690
                                                                    =
                                                                    let uu____25697
                                                                    =
                                                                    let uu____25698
                                                                    =
                                                                    let uu____25709
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    let uu____25717
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25717]
                                                                     in
                                                                    [uu____25714]
                                                                     in
                                                                    let uu____25722
                                                                    =
                                                                    let uu____25723
                                                                    =
                                                                    let uu____25728
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25729
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25728,
                                                                    uu____25729)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25723
                                                                     in
                                                                    (uu____25709,
                                                                    [x],
                                                                    uu____25722)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25698
                                                                     in
                                                                    let uu____25742
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25697,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25742)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25690
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25747
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
                                                                    (let uu____25779
                                                                    =
                                                                    let uu____25780
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25780
                                                                    dapp1  in
                                                                    [uu____25779])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25747
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25787
                                                                    =
                                                                    let uu____25794
                                                                    =
                                                                    let uu____25795
                                                                    =
                                                                    let uu____25806
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25807
                                                                    =
                                                                    let uu____25808
                                                                    =
                                                                    let uu____25813
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25813)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25808
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25806,
                                                                    uu____25807)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25795
                                                                     in
                                                                    (uu____25794,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25787)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____25825 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25825
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25840
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25840
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
                                                                    uu____25891
                                                                    ->
                                                                    let uu____25892
                                                                    =
                                                                    let uu____25897
                                                                    =
                                                                    let uu____25898
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25898
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25897)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25892
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25914
                                                                    =
                                                                    let uu____25915
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25915
                                                                     in
                                                                    if
                                                                    uu____25914
                                                                    then
                                                                    let uu____25928
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25928]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25930
                                                                    =
                                                                    let uu____25943
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25993
                                                                     ->
                                                                    fun
                                                                    uu____25994
                                                                     ->
                                                                    match 
                                                                    (uu____25993,
                                                                    uu____25994)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____26089
                                                                    =
                                                                    let uu____26096
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____26096
                                                                     in
                                                                    (match uu____26089
                                                                    with
                                                                    | 
                                                                    (uu____26109,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____26117
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____26117
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____26119
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____26119
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
                                                                    uu____25943
                                                                     in
                                                                  (match uu____25930
                                                                   with
                                                                   | 
                                                                   (uu____26136,arg_vars,elim_eqns_or_guards,uu____26139)
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
                                                                    let uu____26163
                                                                    =
                                                                    let uu____26170
                                                                    =
                                                                    let uu____26171
                                                                    =
                                                                    let uu____26182
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26183
                                                                    =
                                                                    let uu____26184
                                                                    =
                                                                    let uu____26189
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26189)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26184
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26182,
                                                                    uu____26183)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26171
                                                                     in
                                                                    (uu____26170,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26163
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26199
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26199
                                                                    then
                                                                    let x =
                                                                    let uu____26205
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26205,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26207
                                                                    =
                                                                    let uu____26214
                                                                    =
                                                                    let uu____26215
                                                                    =
                                                                    let uu____26226
                                                                    =
                                                                    let uu____26231
                                                                    =
                                                                    let uu____26234
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26234]
                                                                     in
                                                                    [uu____26231]
                                                                     in
                                                                    let uu____26239
                                                                    =
                                                                    let uu____26240
                                                                    =
                                                                    let uu____26245
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26246
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26245,
                                                                    uu____26246)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26240
                                                                     in
                                                                    (uu____26226,
                                                                    [x],
                                                                    uu____26239)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26215
                                                                     in
                                                                    let uu____26259
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26214,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26259)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26207
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26264
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
                                                                    (let uu____26296
                                                                    =
                                                                    let uu____26297
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26297
                                                                    dapp1  in
                                                                    [uu____26296])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26264
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26304
                                                                    =
                                                                    let uu____26311
                                                                    =
                                                                    let uu____26312
                                                                    =
                                                                    let uu____26323
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26324
                                                                    =
                                                                    let uu____26325
                                                                    =
                                                                    let uu____26330
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26330)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26325
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26323,
                                                                    uu____26324)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26312
                                                                     in
                                                                    (uu____26311,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26304)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____26341 ->
                                                        ((let uu____26343 =
                                                            let uu____26348 =
                                                              let uu____26349
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____26350
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____26349
                                                                uu____26350
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____26348)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26343);
                                                         ([], [])))
                                                in
                                             let uu____26355 = encode_elim ()
                                                in
                                             (match uu____26355 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26381 =
                                                      let uu____26384 =
                                                        let uu____26387 =
                                                          let uu____26390 =
                                                            let uu____26393 =
                                                              let uu____26394
                                                                =
                                                                let uu____26405
                                                                  =
                                                                  let uu____26406
                                                                    =
                                                                    let uu____26407
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26407
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26406
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26405)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26394
                                                               in
                                                            [uu____26393]  in
                                                          let uu____26410 =
                                                            let uu____26413 =
                                                              let uu____26416
                                                                =
                                                                let uu____26419
                                                                  =
                                                                  let uu____26422
                                                                    =
                                                                    let uu____26425
                                                                    =
                                                                    let uu____26428
                                                                    =
                                                                    let uu____26429
                                                                    =
                                                                    let uu____26436
                                                                    =
                                                                    let uu____26437
                                                                    =
                                                                    let uu____26448
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26448)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26437
                                                                     in
                                                                    (uu____26436,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26429
                                                                     in
                                                                    let uu____26457
                                                                    =
                                                                    let uu____26460
                                                                    =
                                                                    let uu____26461
                                                                    =
                                                                    let uu____26468
                                                                    =
                                                                    let uu____26469
                                                                    =
                                                                    let uu____26480
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____26481
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26480,
                                                                    uu____26481)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26469
                                                                     in
                                                                    (uu____26468,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26461
                                                                     in
                                                                    [uu____26460]
                                                                     in
                                                                    uu____26428
                                                                    ::
                                                                    uu____26457
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26425
                                                                     in
                                                                  FStar_List.append
                                                                    uu____26422
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26419
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26416
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26413
                                                             in
                                                          FStar_List.append
                                                            uu____26390
                                                            uu____26410
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____26387
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____26384
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26381
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
           (fun uu____26515  ->
              fun se  ->
                match uu____26515 with
                | (g,env1) ->
                    let uu____26535 = encode_sigelt env1 se  in
                    (match uu____26535 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26600 =
        match uu____26600 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____26632 ->
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
                 ((let uu____26638 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26638
                   then
                     let uu____26639 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26640 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26641 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26639 uu____26640 uu____26641
                   else ());
                  (let uu____26643 = encode_term t1 env1  in
                   match uu____26643 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26659 =
                         let uu____26666 =
                           let uu____26667 =
                             let uu____26668 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26668
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26667  in
                         new_term_constant_from_string env1 x uu____26666  in
                       (match uu____26659 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26682 = FStar_Options.log_queries ()
                                 in
                              if uu____26682
                              then
                                let uu____26683 =
                                  let uu____26684 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26685 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26686 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26684 uu____26685 uu____26686
                                   in
                                FStar_Pervasives_Native.Some uu____26683
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____26698,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26718 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26718 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26741 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26741 with | (uu____26764,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26777 'Auu____26778 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26777,'Auu____26778)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26847  ->
              match uu____26847 with
              | (l,uu____26859,uu____26860) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26904  ->
              match uu____26904 with
              | (l,uu____26918,uu____26919) ->
                  let uu____26928 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26929 =
                    let uu____26932 =
                      let uu____26933 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26933  in
                    [uu____26932]  in
                  uu____26928 :: uu____26929))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____26960 =
      let uu____26963 =
        let uu____26964 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____26967 =
          let uu____26968 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____26968 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26964;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26967
        }  in
      [uu____26963]  in
    FStar_ST.op_Colon_Equals last_env uu____26960
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____27006 = FStar_ST.op_Bang last_env  in
      match uu____27006 with
      | [] -> failwith "No env; call init first!"
      | e::uu____27037 ->
          let uu___134_27040 = e  in
          let uu____27041 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___134_27040.bindings);
            depth = (uu___134_27040.depth);
            tcenv;
            warn = (uu___134_27040.warn);
            cache = (uu___134_27040.cache);
            nolabels = (uu___134_27040.nolabels);
            use_zfuel_name = (uu___134_27040.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_27040.encode_non_total_function_typ);
            current_module_name = uu____27041
          }
  
let (set_env : env_t -> unit) =
  fun env  ->
    let uu____27047 = FStar_ST.op_Bang last_env  in
    match uu____27047 with
    | [] -> failwith "Empty env stack"
    | uu____27077::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____27112  ->
    let uu____27113 = FStar_ST.op_Bang last_env  in
    match uu____27113 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___135_27151 = hd1  in
          {
            bindings = (uu___135_27151.bindings);
            depth = (uu___135_27151.depth);
            tcenv = (uu___135_27151.tcenv);
            warn = (uu___135_27151.warn);
            cache = refs;
            nolabels = (uu___135_27151.nolabels);
            use_zfuel_name = (uu___135_27151.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___135_27151.encode_non_total_function_typ);
            current_module_name = (uu___135_27151.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____27183  ->
    let uu____27184 = FStar_ST.op_Bang last_env  in
    match uu____27184 with
    | [] -> failwith "Popping an empty stack"
    | uu____27214::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____27296::uu____27297,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___136_27305 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___136_27305.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___136_27305.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___136_27305.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27306 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____27325 =
        let uu____27328 =
          let uu____27329 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27329  in
        let uu____27330 = open_fact_db_tags env  in uu____27328 ::
          uu____27330
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27325
  
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
      let uu____27356 = encode_sigelt env se  in
      match uu____27356 with
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
        let uu____27400 = FStar_Options.log_queries ()  in
        if uu____27400
        then
          let uu____27403 =
            let uu____27404 =
              let uu____27405 =
                let uu____27406 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27406 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27405  in
            FStar_SMTEncoding_Term.Caption uu____27404  in
          uu____27403 :: decls
        else decls  in
      (let uu____27417 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27417
       then
         let uu____27418 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27418
       else ());
      (let env =
         let uu____27421 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____27421 tcenv  in
       let uu____27422 = encode_top_level_facts env se  in
       match uu____27422 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27436 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____27436)))
  
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
      (let uu____27452 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27452
       then
         let uu____27453 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27453
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27494  ->
                 fun se  ->
                   match uu____27494 with
                   | (g,env2) ->
                       let uu____27514 = encode_top_level_facts env2 se  in
                       (match uu____27514 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____27537 =
         encode_signature
           (let uu___137_27546 = env  in
            {
              bindings = (uu___137_27546.bindings);
              depth = (uu___137_27546.depth);
              tcenv = (uu___137_27546.tcenv);
              warn = false;
              cache = (uu___137_27546.cache);
              nolabels = (uu___137_27546.nolabels);
              use_zfuel_name = (uu___137_27546.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___137_27546.encode_non_total_function_typ);
              current_module_name = (uu___137_27546.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____27537 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27565 = FStar_Options.log_queries ()  in
             if uu____27565
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___138_27573 = env1  in
               {
                 bindings = (uu___138_27573.bindings);
                 depth = (uu___138_27573.depth);
                 tcenv = (uu___138_27573.tcenv);
                 warn = true;
                 cache = (uu___138_27573.cache);
                 nolabels = (uu___138_27573.nolabels);
                 use_zfuel_name = (uu___138_27573.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___138_27573.encode_non_total_function_typ);
                 current_module_name = (uu___138_27573.current_module_name)
               });
            (let uu____27575 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____27575
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
        (let uu____27633 =
           let uu____27634 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____27634.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27633);
        (let env =
           let uu____27636 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____27636 tcenv  in
         let uu____27637 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____27674 = aux rest  in
                 (match uu____27674 with
                  | (out,rest1) ->
                      let t =
                        let uu____27702 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27702 with
                        | FStar_Pervasives_Native.Some uu____27705 ->
                            let uu____27706 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27706
                              x.FStar_Syntax_Syntax.sort
                        | uu____27707 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27711 =
                        let uu____27714 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___139_27717 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___139_27717.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___139_27717.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27714 :: out  in
                      (uu____27711, rest1))
             | uu____27722 -> ([], bindings)  in
           let uu____27729 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____27729 with
           | (closing,bindings) ->
               let uu____27754 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27754, bindings)
            in
         match uu____27637 with
         | (q1,bindings) ->
             let uu____27777 = encode_env_bindings env bindings  in
             (match uu____27777 with
              | (env_decls,env1) ->
                  ((let uu____27799 =
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
                    if uu____27799
                    then
                      let uu____27800 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27800
                    else ());
                   (let uu____27802 = encode_formula q1 env1  in
                    match uu____27802 with
                    | (phi,qdecls) ->
                        let uu____27823 =
                          let uu____27828 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27828 phi
                           in
                        (match uu____27823 with
                         | (labels,phi1) ->
                             let uu____27845 = encode_labels labels  in
                             (match uu____27845 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27882 =
                                      let uu____27889 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27890 =
                                        varops.mk_unique "@query"  in
                                      (uu____27889,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27890)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27882
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
  