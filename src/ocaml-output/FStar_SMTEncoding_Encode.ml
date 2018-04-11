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
    let uu___105_1865 = x  in
    let uu____1866 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1866;
      FStar_Syntax_Syntax.index = (uu___105_1865.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___105_1865.FStar_Syntax_Syntax.sort)
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
                 (fun uu___82_2418  ->
                    match uu___82_2418 with
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
    let uu____2435 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___83_2445  ->
              match uu___83_2445 with
              | Binding_var (x,uu____2447) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid))
       in
    FStar_All.pipe_right uu____2435 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2457 .
    env_t ->
      (binding -> 'Auu____2457 FStar_Pervasives_Native.option) ->
        'Auu____2457 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2491 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2491
      then
        let uu____2494 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2494
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
      let uu____2511 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2511)
  
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
        (let uu___106_2531 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___106_2531.tcenv);
           warn = (uu___106_2531.warn);
           cache = (uu___106_2531.cache);
           nolabels = (uu___106_2531.nolabels);
           use_zfuel_name = (uu___106_2531.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___106_2531.encode_non_total_function_typ);
           current_module_name = (uu___106_2531.current_module_name)
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
        (let uu___107_2553 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___107_2553.depth);
           tcenv = (uu___107_2553.tcenv);
           warn = (uu___107_2553.warn);
           cache = (uu___107_2553.cache);
           nolabels = (uu___107_2553.nolabels);
           use_zfuel_name = (uu___107_2553.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___107_2553.encode_non_total_function_typ);
           current_module_name = (uu___107_2553.current_module_name)
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
          (let uu___108_2580 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___108_2580.depth);
             tcenv = (uu___108_2580.tcenv);
             warn = (uu___108_2580.warn);
             cache = (uu___108_2580.cache);
             nolabels = (uu___108_2580.nolabels);
             use_zfuel_name = (uu___108_2580.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___108_2580.encode_non_total_function_typ);
             current_module_name = (uu___108_2580.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___109_2596 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___109_2596.depth);
          tcenv = (uu___109_2596.tcenv);
          warn = (uu___109_2596.warn);
          cache = (uu___109_2596.cache);
          nolabels = (uu___109_2596.nolabels);
          use_zfuel_name = (uu___109_2596.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___109_2596.encode_non_total_function_typ);
          current_module_name = (uu___109_2596.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___84_2626  ->
             match uu___84_2626 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2639 -> FStar_Pervasives_Native.None)
         in
      let uu____2644 = aux a  in
      match uu____2644 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2656 = aux a2  in
          (match uu____2656 with
           | FStar_Pervasives_Native.None  ->
               let uu____2667 =
                 let uu____2668 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2669 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2668 uu____2669
                  in
               failwith uu____2667
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
          (let uu___110_2743 = env  in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___110_2743.depth);
             tcenv = (uu___110_2743.tcenv);
             warn = (uu___110_2743.warn);
             cache = (uu___110_2743.cache);
             nolabels = (uu___110_2743.nolabels);
             use_zfuel_name = (uu___110_2743.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___110_2743.encode_non_total_function_typ);
             current_module_name = (uu___110_2743.current_module_name)
           }))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___85_2758  ->
           match uu___85_2758 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2762 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2773 =
        lookup_binding env
          (fun uu___86_2778  ->
             match uu___86_2778 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2782 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2773 FStar_Option.isSome
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2795 = try_lookup_lid env a  in
      match uu____2795 with
      | FStar_Pervasives_Native.None  ->
          let uu____2798 =
            let uu____2799 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2799  in
          failwith uu____2798
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
            let uu___111_2831 = env  in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___111_2831.depth);
              tcenv = (uu___111_2831.tcenv);
              warn = (uu___111_2831.warn);
              cache = (uu___111_2831.cache);
              nolabels = (uu___111_2831.nolabels);
              use_zfuel_name = (uu___111_2831.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___111_2831.encode_non_total_function_typ);
              current_module_name = (uu___111_2831.current_module_name)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2849 =
            let uu____2856 =
              let uu____2859 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2859]  in
            (f, uu____2856)  in
          FStar_SMTEncoding_Util.mkApp uu____2849  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___112_2865 = env  in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___112_2865.depth);
          tcenv = (uu___112_2865.tcenv);
          warn = (uu___112_2865.warn);
          cache = (uu___112_2865.cache);
          nolabels = (uu___112_2865.nolabels);
          use_zfuel_name = (uu___112_2865.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___112_2865.encode_non_total_function_typ);
          current_module_name = (uu___112_2865.current_module_name)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2878 = try_lookup_lid env l  in
      match uu____2878 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2887 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2895,fuel::[]) ->
                         let uu____2899 =
                           let uu____2900 =
                             let uu____2901 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2901
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2900 "fuel"  in
                         if uu____2899
                         then
                           let uu____2904 =
                             let uu____2905 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2905
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_17  ->
                                FStar_Pervasives_Native.Some _0_17)
                             uu____2904
                         else FStar_Pervasives_Native.Some t
                     | uu____2909 -> FStar_Pervasives_Native.Some t)
                | uu____2910 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2927 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2927 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2931 =
            let uu____2932 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2932  in
          failwith uu____2931
  
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
            FStar_SMTEncoding_Term.freevars = uu____2985;
            FStar_SMTEncoding_Term.rng = uu____2986;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____3001 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____3029 ->
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
        (fun uu___87_3046  ->
           match uu___87_3046 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____3050 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3057 .
    'Auu____3057 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3077  ->
      match uu____3077 with
      | (pats,vars,body) ->
          let fallback uu____3104 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3109 = FStar_Options.unthrottle_inductives ()  in
          if uu____3109
          then fallback ()
          else
            (let uu____3111 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3111 with
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
                           | uu____3144 -> p))
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
                             let uu____3165 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3165
                         | uu____3168 ->
                             let uu____3169 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3169 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3174 -> body  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3221 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3234 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3241 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3242 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3259 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3276 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3278 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3278 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3296;
             FStar_Syntax_Syntax.vars = uu____3297;_},uu____3298)
          ->
          let uu____3319 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3319 FStar_Option.isNone
      | uu____3336 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____3347 =
        let uu____3348 = FStar_Syntax_Util.un_uinst t  in
        uu____3348.FStar_Syntax_Syntax.n  in
      match uu____3347 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3351,uu____3352,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___88_3373  ->
                  match uu___88_3373 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3374 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3376 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3376 FStar_Option.isSome
      | uu____3393 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____3404 = head_normal env t  in
      if uu____3404
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
    let uu____3421 =
      let uu____3422 = FStar_Syntax_Syntax.null_binder t  in [uu____3422]  in
    let uu____3423 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3421 uu____3423 FStar_Pervasives_Native.None
  
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
                    let uu____3465 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3465
                | s ->
                    let uu____3468 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3468) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'Auu____3495 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3495
  =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____3516 =
            let uu____3521 =
              let uu____3522 = FStar_Util.string_of_int arity  in
              let uu____3523 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3522 uu____3523
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3521)  in
          FStar_Errors.raise_error uu____3516 rng
  
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
              (let uu____3562 = FStar_Util.first_N arity args  in
               match uu____3562 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3585 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3585 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___89_3594  ->
    match uu___89_3594 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3595 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____3641;
                       FStar_SMTEncoding_Term.rng = uu____3642;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3665) ->
              let uu____3674 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3685 -> false) args (FStar_List.rev xs))
                 in
              if uu____3674
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3689,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3693 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3697 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3697))
                 in
              if uu____3693
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3701 -> FStar_Pervasives_Native.None  in
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
    | uu____3961 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3967 -> false
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3994 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4007 ->
            let uu____4014 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____4014
        | uu____4015 ->
            if norm1
            then let uu____4016 = whnf env t1  in aux false uu____4016
            else
              (let uu____4018 =
                 let uu____4019 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____4020 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4019 uu____4020
                  in
               failwith uu____4018)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4054) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4059 ->
        let uu____4060 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4060)
  
let is_arithmetic_primitive :
  'Auu____4077 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4077 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4099::uu____4100::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4104::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4107 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4130 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4147 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4154 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4154)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4195)::uu____4196::uu____4197::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4248)::uu____4249::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4286 -> false
  
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
          let uu____4589 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4589, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4592 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4592, [])
      | FStar_Const.Const_char c1 ->
          let uu____4596 =
            let uu____4597 =
              let uu____4604 =
                let uu____4607 =
                  let uu____4608 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4608  in
                [uu____4607]  in
              ("FStar.Char.__char_of_int", uu____4604)  in
            FStar_SMTEncoding_Util.mkApp uu____4597  in
          (uu____4596, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4624 =
            let uu____4625 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4625  in
          (uu____4624, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4646) ->
          let uu____4647 = varops.string_const s  in (uu____4647, [])
      | FStar_Const.Const_range uu____4650 ->
          let uu____4651 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4651, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4657 =
            let uu____4658 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4658  in
          failwith uu____4657

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
        (let uu____4687 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4687
         then
           let uu____4688 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4688
         else ());
        (let uu____4690 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4774  ->
                   fun b  ->
                     match uu____4774 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4853 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4869 = gen_term_var env1 x  in
                           match uu____4869 with
                           | (xxsym,xx,env') ->
                               let uu____4893 =
                                 let uu____4898 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4898 env1 xx
                                  in
                               (match uu____4893 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4853 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4690 with
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
          let uu____5057 = encode_term t env  in
          match uu____5057 with
          | (t1,decls) ->
              let uu____5068 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5068, decls)

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
          let uu____5079 = encode_term t env  in
          match uu____5079 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5094 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5094, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5096 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5096, decls))

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
        let uu____5102 = encode_args args_e env  in
        match uu____5102 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5121 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5132 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5132  in
            let binary arg_tms1 =
              let uu____5147 =
                let uu____5148 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5148  in
              let uu____5149 =
                let uu____5150 =
                  let uu____5151 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5151  in
                FStar_SMTEncoding_Term.unboxInt uu____5150  in
              (uu____5147, uu____5149)  in
            let mk_default uu____5159 =
              let uu____5160 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5160 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____5222 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5222
              then
                let uu____5223 =
                  let uu____5224 = mk_args ts  in op uu____5224  in
                FStar_All.pipe_right uu____5223 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5259 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5259
              then
                let uu____5260 = binary ts  in
                match uu____5260 with
                | (t1,t2) ->
                    let uu____5267 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5267
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5271 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5271
                 then
                   let uu____5272 =
                     let uu____5273 = binary ts  in op uu____5273  in
                   FStar_All.pipe_right uu____5272
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
            let uu____5434 =
              let uu____5444 =
                FStar_List.tryFind
                  (fun uu____5468  ->
                     match uu____5468 with
                     | (l,uu____5478) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5444 FStar_Util.must  in
            (match uu____5434 with
             | (uu____5522,op) ->
                 let uu____5534 = op arg_tms  in (uu____5534, decls))

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
        let uu____5542 = FStar_List.hd args_e  in
        match uu____5542 with
        | (tm_sz,uu____5550) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5560 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5560 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____5568 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5568);
                   t_decls1)
               in
            let uu____5569 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5589::(sz_arg,uu____5591)::uu____5592::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5641 =
                    let uu____5644 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5644  in
                  let uu____5647 =
                    let uu____5650 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5650  in
                  (uu____5641, uu____5647)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5656::(sz_arg,uu____5658)::uu____5659::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5708 =
                    let uu____5709 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5709
                     in
                  failwith uu____5708
              | uu____5718 ->
                  let uu____5725 = FStar_List.tail args_e  in
                  (uu____5725, FStar_Pervasives_Native.None)
               in
            (match uu____5569 with
             | (arg_tms,ext_sz) ->
                 let uu____5748 = encode_args arg_tms env  in
                 (match uu____5748 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5769 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5780 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5780  in
                      let unary_arith arg_tms2 =
                        let uu____5791 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5791  in
                      let binary arg_tms2 =
                        let uu____5806 =
                          let uu____5807 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5807
                           in
                        let uu____5808 =
                          let uu____5809 =
                            let uu____5810 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5810  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5809
                           in
                        (uu____5806, uu____5808)  in
                      let binary_arith arg_tms2 =
                        let uu____5827 =
                          let uu____5828 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5828
                           in
                        let uu____5829 =
                          let uu____5830 =
                            let uu____5831 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5831  in
                          FStar_SMTEncoding_Term.unboxInt uu____5830  in
                        (uu____5827, uu____5829)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____5889 =
                          let uu____5890 = mk_args ts  in op uu____5890  in
                        FStar_All.pipe_right uu____5889 resBox  in
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
                        let uu____6022 =
                          let uu____6027 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____6027  in
                        let uu____6029 =
                          let uu____6034 =
                            let uu____6035 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____6035  in
                          FStar_SMTEncoding_Term.boxBitVec uu____6034  in
                        mk_bv uu____6022 unary uu____6029 arg_tms2  in
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
                      let uu____6268 =
                        let uu____6278 =
                          FStar_List.tryFind
                            (fun uu____6302  ->
                               match uu____6302 with
                               | (l,uu____6312) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6278 FStar_Util.must  in
                      (match uu____6268 with
                       | (uu____6358,op) ->
                           let uu____6370 = op arg_tms1  in
                           (uu____6370, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6381 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6381
       then
         let uu____6382 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6383 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6384 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6382 uu____6383
           uu____6384
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6390 ->
           let uu____6415 =
             let uu____6416 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6417 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6418 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6419 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6416
               uu____6417 uu____6418 uu____6419
              in
           failwith uu____6415
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6424 =
             let uu____6425 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6426 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6427 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6428 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6425
               uu____6426 uu____6427 uu____6428
              in
           failwith uu____6424
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6434 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____6434 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6436 =
             let uu____6437 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6437
              in
           failwith uu____6436
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____6444),uu____6445) ->
           let uu____6494 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____6502 -> false  in
           if uu____6494
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____6519) ->
           let tv =
             let uu____6525 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____6525
              in
           let t1 =
             let uu____6529 =
               let uu____6538 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____6538]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____6529
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6540) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6550 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6550, [])
       | FStar_Syntax_Syntax.Tm_type uu____6553 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6557) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6582 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6582 with
            | (binders1,res) ->
                let uu____6593 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6593
                then
                  let uu____6598 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6598 with
                   | (vars,guards,env',decls,uu____6623) ->
                       let fsym =
                         let uu____6641 = varops.fresh "f"  in
                         (uu____6641, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6644 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___113_6653 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___113_6653.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___113_6653.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___113_6653.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___113_6653.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___113_6653.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___113_6653.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___113_6653.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___113_6653.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___113_6653.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___113_6653.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___113_6653.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___113_6653.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___113_6653.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___113_6653.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___113_6653.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___113_6653.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___113_6653.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___113_6653.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___113_6653.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___113_6653.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___113_6653.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___113_6653.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___113_6653.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___113_6653.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___113_6653.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___113_6653.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___113_6653.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___113_6653.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___113_6653.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___113_6653.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___113_6653.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___113_6653.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___113_6653.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___113_6653.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___113_6653.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___113_6653.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6644 with
                        | (pre_opt,res_t) ->
                            let uu____6664 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6664 with
                             | (res_pred,decls') ->
                                 let uu____6675 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6688 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6688, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6692 =
                                         encode_formula pre env'  in
                                       (match uu____6692 with
                                        | (guard,decls0) ->
                                            let uu____6705 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6705, decls0))
                                    in
                                 (match uu____6675 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6717 =
                                          let uu____6728 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6728)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6717
                                         in
                                      let cvars =
                                        let uu____6746 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6746
                                          (FStar_List.filter
                                             (fun uu____6760  ->
                                                match uu____6760 with
                                                | (x,uu____6766) ->
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
                                      let uu____6785 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6785 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6793 =
                                             let uu____6794 =
                                               let uu____6801 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6801)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6794
                                              in
                                           (uu____6793,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6821 =
                                               let uu____6822 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6822
                                                in
                                             varops.mk_unique uu____6821  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6833 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6833
                                             then
                                               let uu____6836 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6836
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
                                             let uu____6844 =
                                               let uu____6851 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6851)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6844
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
                                             let uu____6863 =
                                               let uu____6870 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6870,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6863
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
                                             let uu____6891 =
                                               let uu____6898 =
                                                 let uu____6899 =
                                                   let uu____6910 =
                                                     let uu____6911 =
                                                       let uu____6916 =
                                                         let uu____6917 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6917
                                                          in
                                                       (f_has_t, uu____6916)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6911
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6910)
                                                    in
                                                 mkForall_fuel uu____6899  in
                                               (uu____6898,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6891
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6940 =
                                               let uu____6947 =
                                                 let uu____6948 =
                                                   let uu____6959 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6959)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6948
                                                  in
                                               (uu____6947,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6940
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
                                           ((let uu____6984 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6984);
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
                     let uu____6999 =
                       let uu____7006 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____7006,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6999  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____7018 =
                       let uu____7025 =
                         let uu____7026 =
                           let uu____7037 =
                             let uu____7038 =
                               let uu____7043 =
                                 let uu____7044 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____7044
                                  in
                               (f_has_t, uu____7043)  in
                             FStar_SMTEncoding_Util.mkImp uu____7038  in
                           ([[f_has_t]], [fsym], uu____7037)  in
                         mkForall_fuel uu____7026  in
                       (uu____7025, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____7018  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____7071 ->
           let uu____7078 =
             let uu____7083 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____7083 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____7090;
                 FStar_Syntax_Syntax.vars = uu____7091;_} ->
                 let uu____7098 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____7098 with
                  | (b,f1) ->
                      let uu____7123 =
                        let uu____7124 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7124  in
                      (uu____7123, f1))
             | uu____7133 -> failwith "impossible"  in
           (match uu____7078 with
            | (x,f) ->
                let uu____7144 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7144 with
                 | (base_t,decls) ->
                     let uu____7155 = gen_term_var env x  in
                     (match uu____7155 with
                      | (x1,xtm,env') ->
                          let uu____7169 = encode_formula f env'  in
                          (match uu____7169 with
                           | (refinement,decls') ->
                               let uu____7180 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7180 with
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
                                      let uu____7196 =
                                        let uu____7199 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7206 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7199
                                          uu____7206
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7196
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7239  ->
                                              match uu____7239 with
                                              | (y,uu____7245) ->
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
                                    let uu____7278 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7278 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7286 =
                                           let uu____7287 =
                                             let uu____7294 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7294)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7287
                                            in
                                         (uu____7286,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7315 =
                                             let uu____7316 =
                                               let uu____7317 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7317
                                                in
                                             Prims.strcat module_name
                                               uu____7316
                                              in
                                           varops.mk_unique uu____7315  in
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
                                           let uu____7331 =
                                             let uu____7338 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7338)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7331
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
                                           let uu____7353 =
                                             let uu____7360 =
                                               let uu____7361 =
                                                 let uu____7372 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7372)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7361
                                                in
                                             (uu____7360,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7353
                                            in
                                         let t_kinding =
                                           let uu____7390 =
                                             let uu____7397 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7397,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7390
                                            in
                                         let t_interp =
                                           let uu____7415 =
                                             let uu____7422 =
                                               let uu____7423 =
                                                 let uu____7434 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7434)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7423
                                                in
                                             let uu____7457 =
                                               let uu____7460 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7460
                                                in
                                             (uu____7422, uu____7457,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7415
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7467 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7467);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7497 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7497  in
           let uu____7498 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____7498 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7510 =
                    let uu____7517 =
                      let uu____7518 =
                        let uu____7519 =
                          let uu____7520 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7520
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7519  in
                      varops.mk_unique uu____7518  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7517)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7510  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7525 ->
           let uu____7540 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7540 with
            | (head1,args_e) ->
                let uu____7581 =
                  let uu____7594 =
                    let uu____7595 = FStar_Syntax_Subst.compress head1  in
                    uu____7595.FStar_Syntax_Syntax.n  in
                  (uu____7594, args_e)  in
                (match uu____7581 with
                 | uu____7610 when head_redex env head1 ->
                     let uu____7623 = whnf env t  in
                     encode_term uu____7623 env
                 | uu____7624 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7643 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7657;
                       FStar_Syntax_Syntax.vars = uu____7658;_},uu____7659),uu____7660::
                    (v1,uu____7662)::(v2,uu____7664)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7715 = encode_term v1 env  in
                     (match uu____7715 with
                      | (v11,decls1) ->
                          let uu____7726 = encode_term v2 env  in
                          (match uu____7726 with
                           | (v21,decls2) ->
                               let uu____7737 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7737,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7741::(v1,uu____7743)::(v2,uu____7745)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7792 = encode_term v1 env  in
                     (match uu____7792 with
                      | (v11,decls1) ->
                          let uu____7803 = encode_term v2 env  in
                          (match uu____7803 with
                           | (v21,decls2) ->
                               let uu____7814 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7814,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7818)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7844)::(rng,uu____7846)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7881) ->
                     let e0 =
                       let uu____7899 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7899
                        in
                     ((let uu____7907 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7907
                       then
                         let uu____7908 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7908
                       else ());
                      (let e =
                         let uu____7913 =
                           let uu____7918 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7919 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7918
                             uu____7919
                            in
                         uu____7913 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7928),(arg,uu____7930)::[]) -> encode_term arg env
                 | uu____7955 ->
                     let uu____7968 = encode_args args_e env  in
                     (match uu____7968 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____8025 = encode_term head1 env  in
                            match uu____8025 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____8089 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____8089 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8167  ->
                                                 fun uu____8168  ->
                                                   match (uu____8167,
                                                           uu____8168)
                                                   with
                                                   | ((bv,uu____8190),
                                                      (a,uu____8192)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8210 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8210
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8215 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8215 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8230 =
                                                   let uu____8237 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8246 =
                                                     let uu____8247 =
                                                       let uu____8248 =
                                                         let uu____8249 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8249
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8248
                                                        in
                                                     varops.mk_unique
                                                       uu____8247
                                                      in
                                                   (uu____8237,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8246)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8230
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8268 = lookup_free_var_sym env fv  in
                            match uu____8268 with
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
                                   FStar_Syntax_Syntax.pos = uu____8300;
                                   FStar_Syntax_Syntax.vars = uu____8301;_},uu____8302)
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
                                   FStar_Syntax_Syntax.pos = uu____8313;
                                   FStar_Syntax_Syntax.vars = uu____8314;_},uu____8315)
                                ->
                                let uu____8320 =
                                  let uu____8321 =
                                    let uu____8326 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8326
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8321
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8320
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8356 =
                                  let uu____8357 =
                                    let uu____8362 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8362
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8357
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8356
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8391,(FStar_Util.Inl t1,uu____8393),uu____8394)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8443,(FStar_Util.Inr c,uu____8445),uu____8446)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8495 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8522 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8522
                                  in
                               let uu____8523 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8523 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8539;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8540;_},uu____8541)
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
                                     | uu____8555 ->
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
           let uu____8604 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8604 with
            | (bs1,body1,opening) ->
                let fallback uu____8629 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8636 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8636, [decl])  in
                let is_impure rc =
                  let uu____8645 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8645 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8657 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____8657
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8675 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8675
                  then
                    let uu____8678 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8678
                  else
                    (let uu____8680 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8680
                     then
                       let uu____8683 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8683
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8690 =
                         let uu____8695 =
                           let uu____8696 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8696
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8695)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8690);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8698 =
                       (is_impure rc) &&
                         (let uu____8700 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8700)
                        in
                     if uu____8698
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8707 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8707 with
                        | (vars,guards,envbody,decls,uu____8732) ->
                            let body2 =
                              let uu____8746 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8746
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8748 = encode_term body2 envbody  in
                            (match uu____8748 with
                             | (body3,decls') ->
                                 let uu____8759 =
                                   let uu____8768 = codomain_eff rc  in
                                   match uu____8768 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8787 = encode_term tfun env
                                          in
                                       (match uu____8787 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8759 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8819 =
                                          let uu____8830 =
                                            let uu____8831 =
                                              let uu____8836 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8836, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8831
                                             in
                                          ([], vars, uu____8830)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8819
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
                                            let uu____8848 =
                                              let uu____8851 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8851
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8848
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8870 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8870 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8878 =
                                             let uu____8879 =
                                               let uu____8886 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8886)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8879
                                              in
                                           (uu____8878,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8897 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8897 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8908 =
                                                    let uu____8909 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8909 = cache_size
                                                     in
                                                  if uu____8908
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
                                                    let uu____8925 =
                                                      let uu____8926 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8926
                                                       in
                                                    varops.mk_unique
                                                      uu____8925
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
                                                  let uu____8933 =
                                                    let uu____8940 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8940)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8933
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
                                                      let uu____8958 =
                                                        let uu____8959 =
                                                          let uu____8966 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8966,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8959
                                                         in
                                                      [uu____8958]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8979 =
                                                    let uu____8986 =
                                                      let uu____8987 =
                                                        let uu____8998 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8998)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8987
                                                       in
                                                    (uu____8986,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8979
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
                                                ((let uu____9015 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____9015);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____9018,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____9019;
                          FStar_Syntax_Syntax.lbunivs = uu____9020;
                          FStar_Syntax_Syntax.lbtyp = uu____9021;
                          FStar_Syntax_Syntax.lbeff = uu____9022;
                          FStar_Syntax_Syntax.lbdef = uu____9023;
                          FStar_Syntax_Syntax.lbattrs = uu____9024;
                          FStar_Syntax_Syntax.lbpos = uu____9025;_}::uu____9026),uu____9027)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____9057;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____9059;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____9061;
                FStar_Syntax_Syntax.lbpos = uu____9062;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____9086 ->
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
              let uu____9156 =
                let uu____9161 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9161 env  in
              match uu____9156 with
              | (ee1,decls1) ->
                  let uu____9182 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9182 with
                   | (xs,e21) ->
                       let uu____9207 = FStar_List.hd xs  in
                       (match uu____9207 with
                        | (x1,uu____9221) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9223 = encode_body e21 env'  in
                            (match uu____9223 with
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
            let uu____9255 =
              let uu____9262 =
                let uu____9263 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9263  in
              gen_term_var env uu____9262  in
            match uu____9255 with
            | (scrsym,scr',env1) ->
                let uu____9271 = encode_term e env1  in
                (match uu____9271 with
                 | (scr,decls) ->
                     let uu____9282 =
                       let encode_branch b uu____9311 =
                         match uu____9311 with
                         | (else_case,decls1) ->
                             let uu____9330 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9330 with
                              | (p,w,br) ->
                                  let uu____9356 = encode_pat env1 p  in
                                  (match uu____9356 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9393  ->
                                                   match uu____9393 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9400 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9422 =
                                               encode_term w1 env2  in
                                             (match uu____9422 with
                                              | (w2,decls2) ->
                                                  let uu____9435 =
                                                    let uu____9436 =
                                                      let uu____9441 =
                                                        let uu____9442 =
                                                          let uu____9447 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9447)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9442
                                                         in
                                                      (guard, uu____9441)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9436
                                                     in
                                                  (uu____9435, decls2))
                                          in
                                       (match uu____9400 with
                                        | (guard1,decls2) ->
                                            let uu____9460 =
                                              encode_br br env2  in
                                            (match uu____9460 with
                                             | (br1,decls3) ->
                                                 let uu____9473 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9473,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9282 with
                      | (match_tm,decls1) ->
                          let uu____9492 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9492, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____9532 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9532
       then
         let uu____9533 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9533
       else ());
      (let uu____9535 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9535 with
       | (vars,pat_term) ->
           let uu____9552 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9605  ->
                     fun v1  ->
                       match uu____9605 with
                       | (env1,vars1) ->
                           let uu____9657 = gen_term_var env1 v1  in
                           (match uu____9657 with
                            | (xx,uu____9679,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9552 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9762 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9763 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9764 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9772 = encode_const c env1  in
                      (match uu____9772 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9786::uu____9787 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9790 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9813 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9813 with
                        | (uu____9820,uu____9821::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9824 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9857  ->
                                  match uu____9857 with
                                  | (arg,uu____9865) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9871 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9871))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9902) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9933 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9956 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____10000  ->
                                  match uu____10000 with
                                  | (arg,uu____10014) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____10020 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____10020))
                         in
                      FStar_All.pipe_right uu____9956 FStar_List.flatten
                   in
                let pat_term1 uu____10050 = encode_term pat_term env1  in
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
      let uu____10060 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10098  ->
                fun uu____10099  ->
                  match (uu____10098, uu____10099) with
                  | ((tms,decls),(t,uu____10135)) ->
                      let uu____10156 = encode_term t env  in
                      (match uu____10156 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10060 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10215 = FStar_Syntax_Util.list_elements e  in
        match uu____10215 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____10238 =
          let uu____10253 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10253 FStar_Syntax_Util.head_and_args
           in
        match uu____10238 with
        | (head1,args) ->
            let uu____10292 =
              let uu____10305 =
                let uu____10306 = FStar_Syntax_Util.un_uinst head1  in
                uu____10306.FStar_Syntax_Syntax.n  in
              (uu____10305, args)  in
            (match uu____10292 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10320,uu____10321)::(e,uu____10323)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10358 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____10398 =
            let uu____10413 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10413 FStar_Syntax_Util.head_and_args
             in
          match uu____10398 with
          | (head1,args) ->
              let uu____10454 =
                let uu____10467 =
                  let uu____10468 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10468.FStar_Syntax_Syntax.n  in
                (uu____10467, args)  in
              (match uu____10454 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10485)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10512 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10534 = smt_pat_or t1  in
            (match uu____10534 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10550 = list_elements1 e  in
                 FStar_All.pipe_right uu____10550
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10568 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10568
                           (FStar_List.map one_pat)))
             | uu____10579 ->
                 let uu____10584 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10584])
        | uu____10605 ->
            let uu____10608 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10608]
         in
      let uu____10629 =
        let uu____10648 =
          let uu____10649 = FStar_Syntax_Subst.compress t  in
          uu____10649.FStar_Syntax_Syntax.n  in
        match uu____10648 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10688 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10688 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10731;
                        FStar_Syntax_Syntax.effect_name = uu____10732;
                        FStar_Syntax_Syntax.result_typ = uu____10733;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10735)::(post,uu____10737)::(pats,uu____10739)::[];
                        FStar_Syntax_Syntax.flags = uu____10740;_}
                      ->
                      let uu____10781 = lemma_pats pats  in
                      (binders1, pre, post, uu____10781)
                  | uu____10798 -> failwith "impos"))
        | uu____10817 -> failwith "Impos"  in
      match uu____10629 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___114_10865 = env  in
            {
              bindings = (uu___114_10865.bindings);
              depth = (uu___114_10865.depth);
              tcenv = (uu___114_10865.tcenv);
              warn = (uu___114_10865.warn);
              cache = (uu___114_10865.cache);
              nolabels = (uu___114_10865.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___114_10865.encode_non_total_function_typ);
              current_module_name = (uu___114_10865.current_module_name)
            }  in
          let uu____10866 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10866 with
           | (vars,guards,env2,decls,uu____10891) ->
               let uu____10904 =
                 let uu____10919 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10973 =
                             let uu____10984 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10984
                               FStar_List.unzip
                              in
                           match uu____10973 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10919 FStar_List.unzip  in
               (match uu____10904 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___115_11136 = env2  in
                      {
                        bindings = (uu___115_11136.bindings);
                        depth = (uu___115_11136.depth);
                        tcenv = (uu___115_11136.tcenv);
                        warn = (uu___115_11136.warn);
                        cache = (uu___115_11136.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___115_11136.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___115_11136.encode_non_total_function_typ);
                        current_module_name =
                          (uu___115_11136.current_module_name)
                      }  in
                    let uu____11137 =
                      let uu____11142 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____11142 env3  in
                    (match uu____11137 with
                     | (pre1,decls'') ->
                         let uu____11149 =
                           let uu____11154 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____11154 env3  in
                         (match uu____11149 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____11164 =
                                let uu____11165 =
                                  let uu____11176 =
                                    let uu____11177 =
                                      let uu____11182 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____11182, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____11177
                                     in
                                  (pats, vars, uu____11176)  in
                                FStar_SMTEncoding_Util.mkForall uu____11165
                                 in
                              (uu____11164, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11195 = FStar_Syntax_Util.head_and_args t  in
      match uu____11195 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11254::(x,uu____11256)::(t1,uu____11258)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11305 = encode_term x env  in
               (match uu____11305 with
                | (x1,decls) ->
                    let uu____11318 = encode_term t1 env  in
                    (match uu____11318 with
                     | (t2,decls') ->
                         let uu____11331 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11331, (FStar_List.append decls decls'))))
           | uu____11334 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11359 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11359
        then
          let uu____11360 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11361 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11360 uu____11361
        else ()  in
      let enc f r l =
        let uu____11400 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11428 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11428 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11400 with
        | (decls,args) ->
            let uu____11457 =
              let uu___116_11458 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___116_11458.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___116_11458.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11457, decls)
         in
      let const_op f r uu____11495 =
        let uu____11508 = f r  in (uu____11508, [])  in
      let un_op f l =
        let uu____11531 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11531  in
      let bin_op f uu___90_11551 =
        match uu___90_11551 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11562 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11602 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11625  ->
                 match uu____11625 with
                 | (t,uu____11639) ->
                     let uu____11640 = encode_formula t env  in
                     (match uu____11640 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11602 with
        | (decls,phis) ->
            let uu____11669 =
              let uu___117_11670 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11670.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11670.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11669, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11735  ->
               match uu____11735 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11754) -> false
                    | uu____11755 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11770 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11770
        else
          (let uu____11784 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11784 r rf)
         in
      let mk_imp1 r uu___91_11819 =
        match uu___91_11819 with
        | (lhs,uu____11825)::(rhs,uu____11827)::[] ->
            let uu____11854 = encode_formula rhs env  in
            (match uu____11854 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11869) ->
                      (l1, decls1)
                  | uu____11874 ->
                      let uu____11875 = encode_formula lhs env  in
                      (match uu____11875 with
                       | (l2,decls2) ->
                           let uu____11886 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11886, (FStar_List.append decls1 decls2)))))
        | uu____11889 -> failwith "impossible"  in
      let mk_ite r uu___92_11916 =
        match uu___92_11916 with
        | (guard,uu____11922)::(_then,uu____11924)::(_else,uu____11926)::[]
            ->
            let uu____11963 = encode_formula guard env  in
            (match uu____11963 with
             | (g,decls1) ->
                 let uu____11974 = encode_formula _then env  in
                 (match uu____11974 with
                  | (t,decls2) ->
                      let uu____11985 = encode_formula _else env  in
                      (match uu____11985 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11999 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____12028 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____12028  in
      let connectives =
        let uu____12048 =
          let uu____12063 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____12063)  in
        let uu____12086 =
          let uu____12103 =
            let uu____12118 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____12118)  in
          let uu____12141 =
            let uu____12158 =
              let uu____12176 =
                let uu____12191 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12191)  in
              let uu____12214 =
                let uu____12231 =
                  let uu____12249 =
                    let uu____12264 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12264)  in
                  [uu____12249;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12231  in
              uu____12176 :: uu____12214  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____12158  in
          uu____12103 :: uu____12141  in
        uu____12048 :: uu____12086  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12631 = encode_formula phi' env  in
            (match uu____12631 with
             | (phi2,decls) ->
                 let uu____12642 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12642, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12643 ->
            let uu____12650 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12650 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12689 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12689 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12701;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12703;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12705;
                 FStar_Syntax_Syntax.lbpos = uu____12706;_}::[]),e2)
            ->
            let uu____12730 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12730 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12777::(x,uu____12779)::(t,uu____12781)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12828 = encode_term x env  in
                 (match uu____12828 with
                  | (x1,decls) ->
                      let uu____12839 = encode_term t env  in
                      (match uu____12839 with
                       | (t1,decls') ->
                           let uu____12850 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12850, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12855)::(msg,uu____12857)::(phi2,uu____12859)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12904 =
                   let uu____12909 =
                     let uu____12910 = FStar_Syntax_Subst.compress r  in
                     uu____12910.FStar_Syntax_Syntax.n  in
                   let uu____12913 =
                     let uu____12914 = FStar_Syntax_Subst.compress msg  in
                     uu____12914.FStar_Syntax_Syntax.n  in
                   (uu____12909, uu____12913)  in
                 (match uu____12904 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12923))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12929 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12936)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12961 when head_redex env head2 ->
                 let uu____12974 = whnf env phi1  in
                 encode_formula uu____12974 env
             | uu____12975 ->
                 let uu____12988 = encode_term phi1 env  in
                 (match uu____12988 with
                  | (tt,decls) ->
                      let uu____12999 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___118_13002 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___118_13002.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___118_13002.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12999, decls)))
        | uu____13003 ->
            let uu____13004 = encode_term phi1 env  in
            (match uu____13004 with
             | (tt,decls) ->
                 let uu____13015 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___119_13018 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___119_13018.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___119_13018.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____13015, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____13062 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____13062 with
        | (vars,guards,env2,decls,uu____13101) ->
            let uu____13114 =
              let uu____13127 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____13179 =
                          let uu____13190 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____13230  ->
                                    match uu____13230 with
                                    | (t,uu____13244) ->
                                        encode_smt_pattern t
                                          (let uu___120_13250 = env2  in
                                           {
                                             bindings =
                                               (uu___120_13250.bindings);
                                             depth = (uu___120_13250.depth);
                                             tcenv = (uu___120_13250.tcenv);
                                             warn = (uu___120_13250.warn);
                                             cache = (uu___120_13250.cache);
                                             nolabels =
                                               (uu___120_13250.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___120_13250.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___120_13250.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____13190 FStar_List.unzip
                           in
                        match uu____13179 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____13127 FStar_List.unzip  in
            (match uu____13114 with
             | (pats,decls') ->
                 let uu____13359 = encode_formula body env2  in
                 (match uu____13359 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13391;
                             FStar_SMTEncoding_Term.rng = uu____13392;_}::[])::[]
                            when
                            let uu____13407 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13407 = gf -> []
                        | uu____13408 -> guards  in
                      let uu____13413 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13413, body1,
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
                (fun uu____13477  ->
                   match uu____13477 with
                   | (x,uu____13483) ->
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
               let uu____13491 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13503 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____13503) uu____13491 tl1
                in
             let uu____13506 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13533  ->
                       match uu____13533 with
                       | (b,uu____13539) ->
                           let uu____13540 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____13540))
                in
             (match uu____13506 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13546) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____13560 =
                    let uu____13565 =
                      let uu____13566 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____13566
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____13565)
                     in
                  FStar_Errors.log_issue pos uu____13560)
          in
       let uu____13567 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13567 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13576 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13642  ->
                     match uu____13642 with
                     | (l,uu____13656) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13576 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13695,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13741 = encode_q_body env vars pats body  in
             match uu____13741 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13786 =
                     let uu____13797 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13797)  in
                   FStar_SMTEncoding_Term.mkForall uu____13786
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13816 = encode_q_body env vars pats body  in
             match uu____13816 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13860 =
                   let uu____13861 =
                     let uu____13872 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13872)  in
                   FStar_SMTEncoding_Term.mkExists uu____13861
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13860, decls))))

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
  let uu____13999 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13999 with
  | (asym,a) ->
      let uu____14006 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____14006 with
       | (xsym,x) ->
           let uu____14013 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____14013 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____14067 =
                      let uu____14078 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____14078, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____14067  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____14104 =
                      let uu____14111 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____14111)  in
                    FStar_SMTEncoding_Util.mkApp uu____14104  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____14124 =
                    let uu____14127 =
                      let uu____14130 =
                        let uu____14133 =
                          let uu____14134 =
                            let uu____14141 =
                              let uu____14142 =
                                let uu____14153 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____14153)  in
                              FStar_SMTEncoding_Util.mkForall uu____14142  in
                            (uu____14141, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____14134  in
                        let uu____14170 =
                          let uu____14173 =
                            let uu____14174 =
                              let uu____14181 =
                                let uu____14182 =
                                  let uu____14193 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____14193)  in
                                FStar_SMTEncoding_Util.mkForall uu____14182
                                 in
                              (uu____14181,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____14174  in
                          [uu____14173]  in
                        uu____14133 :: uu____14170  in
                      xtok_decl :: uu____14130  in
                    xname_decl :: uu____14127  in
                  (xtok1, (FStar_List.length vars), uu____14124)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____14291 =
                    let uu____14307 =
                      let uu____14320 =
                        let uu____14321 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____14321
                         in
                      quant axy uu____14320  in
                    (FStar_Parser_Const.op_Eq, uu____14307)  in
                  let uu____14333 =
                    let uu____14351 =
                      let uu____14367 =
                        let uu____14380 =
                          let uu____14381 =
                            let uu____14382 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14382  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14381
                           in
                        quant axy uu____14380  in
                      (FStar_Parser_Const.op_notEq, uu____14367)  in
                    let uu____14394 =
                      let uu____14412 =
                        let uu____14428 =
                          let uu____14441 =
                            let uu____14442 =
                              let uu____14443 =
                                let uu____14448 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14449 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14448, uu____14449)  in
                              FStar_SMTEncoding_Util.mkLT uu____14443  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14442
                             in
                          quant xy uu____14441  in
                        (FStar_Parser_Const.op_LT, uu____14428)  in
                      let uu____14461 =
                        let uu____14479 =
                          let uu____14495 =
                            let uu____14508 =
                              let uu____14509 =
                                let uu____14510 =
                                  let uu____14515 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14516 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14515, uu____14516)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14510  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14509
                               in
                            quant xy uu____14508  in
                          (FStar_Parser_Const.op_LTE, uu____14495)  in
                        let uu____14528 =
                          let uu____14546 =
                            let uu____14562 =
                              let uu____14575 =
                                let uu____14576 =
                                  let uu____14577 =
                                    let uu____14582 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14583 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14582, uu____14583)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14577  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14576
                                 in
                              quant xy uu____14575  in
                            (FStar_Parser_Const.op_GT, uu____14562)  in
                          let uu____14595 =
                            let uu____14613 =
                              let uu____14629 =
                                let uu____14642 =
                                  let uu____14643 =
                                    let uu____14644 =
                                      let uu____14649 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14650 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14649, uu____14650)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14644
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14643
                                   in
                                quant xy uu____14642  in
                              (FStar_Parser_Const.op_GTE, uu____14629)  in
                            let uu____14662 =
                              let uu____14680 =
                                let uu____14696 =
                                  let uu____14709 =
                                    let uu____14710 =
                                      let uu____14711 =
                                        let uu____14716 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14717 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14716, uu____14717)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14711
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14710
                                     in
                                  quant xy uu____14709  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14696)
                                 in
                              let uu____14729 =
                                let uu____14747 =
                                  let uu____14763 =
                                    let uu____14776 =
                                      let uu____14777 =
                                        let uu____14778 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14778
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14777
                                       in
                                    quant qx uu____14776  in
                                  (FStar_Parser_Const.op_Minus, uu____14763)
                                   in
                                let uu____14790 =
                                  let uu____14808 =
                                    let uu____14824 =
                                      let uu____14837 =
                                        let uu____14838 =
                                          let uu____14839 =
                                            let uu____14844 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14845 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14844, uu____14845)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14839
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14838
                                         in
                                      quant xy uu____14837  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14824)
                                     in
                                  let uu____14857 =
                                    let uu____14875 =
                                      let uu____14891 =
                                        let uu____14904 =
                                          let uu____14905 =
                                            let uu____14906 =
                                              let uu____14911 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14912 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14911, uu____14912)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14906
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14905
                                           in
                                        quant xy uu____14904  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14891)
                                       in
                                    let uu____14924 =
                                      let uu____14942 =
                                        let uu____14958 =
                                          let uu____14971 =
                                            let uu____14972 =
                                              let uu____14973 =
                                                let uu____14978 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14979 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14978, uu____14979)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14973
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14972
                                             in
                                          quant xy uu____14971  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14958)
                                         in
                                      let uu____14991 =
                                        let uu____15009 =
                                          let uu____15025 =
                                            let uu____15038 =
                                              let uu____15039 =
                                                let uu____15040 =
                                                  let uu____15045 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____15046 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____15045, uu____15046)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____15040
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____15039
                                               in
                                            quant xy uu____15038  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____15025)
                                           in
                                        let uu____15058 =
                                          let uu____15076 =
                                            let uu____15092 =
                                              let uu____15105 =
                                                let uu____15106 =
                                                  let uu____15107 =
                                                    let uu____15112 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____15113 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____15112,
                                                      uu____15113)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15107
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____15106
                                                 in
                                              quant xy uu____15105  in
                                            (FStar_Parser_Const.op_And,
                                              uu____15092)
                                             in
                                          let uu____15125 =
                                            let uu____15143 =
                                              let uu____15159 =
                                                let uu____15172 =
                                                  let uu____15173 =
                                                    let uu____15174 =
                                                      let uu____15179 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____15180 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____15179,
                                                        uu____15180)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____15174
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____15173
                                                   in
                                                quant xy uu____15172  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____15159)
                                               in
                                            let uu____15192 =
                                              let uu____15210 =
                                                let uu____15226 =
                                                  let uu____15239 =
                                                    let uu____15240 =
                                                      let uu____15241 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____15241
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____15240
                                                     in
                                                  quant qx uu____15239  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____15226)
                                                 in
                                              [uu____15210]  in
                                            uu____15143 :: uu____15192  in
                                          uu____15076 :: uu____15125  in
                                        uu____15009 :: uu____15058  in
                                      uu____14942 :: uu____14991  in
                                    uu____14875 :: uu____14924  in
                                  uu____14808 :: uu____14857  in
                                uu____14747 :: uu____14790  in
                              uu____14680 :: uu____14729  in
                            uu____14613 :: uu____14662  in
                          uu____14546 :: uu____14595  in
                        uu____14479 :: uu____14528  in
                      uu____14412 :: uu____14461  in
                    uu____14351 :: uu____14394  in
                  uu____14291 :: uu____14333  in
                let mk1 l v1 =
                  let uu____15512 =
                    let uu____15523 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15593  ->
                              match uu____15593 with
                              | (l',uu____15609) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____15523
                      (FStar_Option.map
                         (fun uu____15685  ->
                            match uu____15685 with | (uu____15708,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____15512 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15799  ->
                          match uu____15799 with
                          | (l',uu____15815) -> FStar_Ident.lid_equals l l'))
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
        let uu____15865 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15865 with
        | (xxsym,xx) ->
            let uu____15872 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15872 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15882 =
                   let uu____15889 =
                     let uu____15890 =
                       let uu____15901 =
                         let uu____15902 =
                           let uu____15907 =
                             let uu____15908 =
                               let uu____15913 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15913)  in
                             FStar_SMTEncoding_Util.mkEq uu____15908  in
                           (xx_has_type, uu____15907)  in
                         FStar_SMTEncoding_Util.mkImp uu____15902  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15901)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15890  in
                   let uu____15938 =
                     let uu____15939 =
                       let uu____15940 =
                         let uu____15941 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15941  in
                       Prims.strcat module_name uu____15940  in
                     varops.mk_unique uu____15939  in
                   (uu____15889, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15938)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15882)
  
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
    let uu____15991 =
      let uu____15992 =
        let uu____15999 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15999, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15992  in
    let uu____16002 =
      let uu____16005 =
        let uu____16006 =
          let uu____16013 =
            let uu____16014 =
              let uu____16025 =
                let uu____16026 =
                  let uu____16031 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____16031)  in
                FStar_SMTEncoding_Util.mkImp uu____16026  in
              ([[typing_pred]], [xx], uu____16025)  in
            mkForall_fuel uu____16014  in
          (uu____16013, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16006  in
      [uu____16005]  in
    uu____15991 :: uu____16002  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16079 =
      let uu____16080 =
        let uu____16087 =
          let uu____16088 =
            let uu____16099 =
              let uu____16104 =
                let uu____16107 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____16107]  in
              [uu____16104]  in
            let uu____16112 =
              let uu____16113 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16113 tt  in
            (uu____16099, [bb], uu____16112)  in
          FStar_SMTEncoding_Util.mkForall uu____16088  in
        (uu____16087, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16080  in
    let uu____16134 =
      let uu____16137 =
        let uu____16138 =
          let uu____16145 =
            let uu____16146 =
              let uu____16157 =
                let uu____16158 =
                  let uu____16163 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____16163)  in
                FStar_SMTEncoding_Util.mkImp uu____16158  in
              ([[typing_pred]], [xx], uu____16157)  in
            mkForall_fuel uu____16146  in
          (uu____16145, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16138  in
      [uu____16137]  in
    uu____16079 :: uu____16134  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____16219 =
        let uu____16220 =
          let uu____16227 =
            let uu____16230 =
              let uu____16233 =
                let uu____16236 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____16237 =
                  let uu____16240 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____16240]  in
                uu____16236 :: uu____16237  in
              tt :: uu____16233  in
            tt :: uu____16230  in
          ("Prims.Precedes", uu____16227)  in
        FStar_SMTEncoding_Util.mkApp uu____16220  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16219  in
    let precedes_y_x =
      let uu____16244 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____16244  in
    let uu____16247 =
      let uu____16248 =
        let uu____16255 =
          let uu____16256 =
            let uu____16267 =
              let uu____16272 =
                let uu____16275 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____16275]  in
              [uu____16272]  in
            let uu____16280 =
              let uu____16281 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16281 tt  in
            (uu____16267, [bb], uu____16280)  in
          FStar_SMTEncoding_Util.mkForall uu____16256  in
        (uu____16255, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16248  in
    let uu____16302 =
      let uu____16305 =
        let uu____16306 =
          let uu____16313 =
            let uu____16314 =
              let uu____16325 =
                let uu____16326 =
                  let uu____16331 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____16331)  in
                FStar_SMTEncoding_Util.mkImp uu____16326  in
              ([[typing_pred]], [xx], uu____16325)  in
            mkForall_fuel uu____16314  in
          (uu____16313, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16306  in
      let uu____16356 =
        let uu____16359 =
          let uu____16360 =
            let uu____16367 =
              let uu____16368 =
                let uu____16379 =
                  let uu____16380 =
                    let uu____16385 =
                      let uu____16386 =
                        let uu____16389 =
                          let uu____16392 =
                            let uu____16395 =
                              let uu____16396 =
                                let uu____16401 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____16402 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____16401, uu____16402)  in
                              FStar_SMTEncoding_Util.mkGT uu____16396  in
                            let uu____16403 =
                              let uu____16406 =
                                let uu____16407 =
                                  let uu____16412 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____16413 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____16412, uu____16413)  in
                                FStar_SMTEncoding_Util.mkGTE uu____16407  in
                              let uu____16414 =
                                let uu____16417 =
                                  let uu____16418 =
                                    let uu____16423 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____16424 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____16423, uu____16424)  in
                                  FStar_SMTEncoding_Util.mkLT uu____16418  in
                                [uu____16417]  in
                              uu____16406 :: uu____16414  in
                            uu____16395 :: uu____16403  in
                          typing_pred_y :: uu____16392  in
                        typing_pred :: uu____16389  in
                      FStar_SMTEncoding_Util.mk_and_l uu____16386  in
                    (uu____16385, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____16380  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____16379)
                 in
              mkForall_fuel uu____16368  in
            (uu____16367,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____16360  in
        [uu____16359]  in
      uu____16305 :: uu____16356  in
    uu____16247 :: uu____16302  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16476 =
      let uu____16477 =
        let uu____16484 =
          let uu____16485 =
            let uu____16496 =
              let uu____16501 =
                let uu____16504 = FStar_SMTEncoding_Term.boxString b  in
                [uu____16504]  in
              [uu____16501]  in
            let uu____16509 =
              let uu____16510 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16510 tt  in
            (uu____16496, [bb], uu____16509)  in
          FStar_SMTEncoding_Util.mkForall uu____16485  in
        (uu____16484, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16477  in
    let uu____16531 =
      let uu____16534 =
        let uu____16535 =
          let uu____16542 =
            let uu____16543 =
              let uu____16554 =
                let uu____16555 =
                  let uu____16560 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____16560)  in
                FStar_SMTEncoding_Util.mkImp uu____16555  in
              ([[typing_pred]], [xx], uu____16554)  in
            mkForall_fuel uu____16543  in
          (uu____16542, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16535  in
      [uu____16534]  in
    uu____16476 :: uu____16531  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____16625 =
      let uu____16626 =
        let uu____16633 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____16633, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16626  in
    [uu____16625]  in
  let mk_and_interp env conj uu____16651 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16676 =
      let uu____16677 =
        let uu____16684 =
          let uu____16685 =
            let uu____16696 =
              let uu____16697 =
                let uu____16702 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16702, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16697  in
            ([[l_and_a_b]], [aa; bb], uu____16696)  in
          FStar_SMTEncoding_Util.mkForall uu____16685  in
        (uu____16684, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16677  in
    [uu____16676]  in
  let mk_or_interp env disj uu____16746 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16771 =
      let uu____16772 =
        let uu____16779 =
          let uu____16780 =
            let uu____16791 =
              let uu____16792 =
                let uu____16797 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16797, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16792  in
            ([[l_or_a_b]], [aa; bb], uu____16791)  in
          FStar_SMTEncoding_Util.mkForall uu____16780  in
        (uu____16779, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16772  in
    [uu____16771]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16866 =
      let uu____16867 =
        let uu____16874 =
          let uu____16875 =
            let uu____16886 =
              let uu____16887 =
                let uu____16892 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16892, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16887  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16886)  in
          FStar_SMTEncoding_Util.mkForall uu____16875  in
        (uu____16874, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16867  in
    [uu____16866]  in
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
    let uu____16971 =
      let uu____16972 =
        let uu____16979 =
          let uu____16980 =
            let uu____16991 =
              let uu____16992 =
                let uu____16997 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16997, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16992  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16991)  in
          FStar_SMTEncoding_Util.mkForall uu____16980  in
        (uu____16979, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16972  in
    [uu____16971]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____17074 =
      let uu____17075 =
        let uu____17082 =
          let uu____17083 =
            let uu____17094 =
              let uu____17095 =
                let uu____17100 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____17100, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17095  in
            ([[l_imp_a_b]], [aa; bb], uu____17094)  in
          FStar_SMTEncoding_Util.mkForall uu____17083  in
        (uu____17082, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17075  in
    [uu____17074]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____17169 =
      let uu____17170 =
        let uu____17177 =
          let uu____17178 =
            let uu____17189 =
              let uu____17190 =
                let uu____17195 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____17195, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17190  in
            ([[l_iff_a_b]], [aa; bb], uu____17189)  in
          FStar_SMTEncoding_Util.mkForall uu____17178  in
        (uu____17177, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17170  in
    [uu____17169]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____17253 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____17253  in
    let uu____17256 =
      let uu____17257 =
        let uu____17264 =
          let uu____17265 =
            let uu____17276 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____17276)  in
          FStar_SMTEncoding_Util.mkForall uu____17265  in
        (uu____17264, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17257  in
    [uu____17256]  in
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
      let uu____17342 =
        let uu____17349 =
          let uu____17352 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17352]  in
        ("Valid", uu____17349)  in
      FStar_SMTEncoding_Util.mkApp uu____17342  in
    let uu____17355 =
      let uu____17356 =
        let uu____17363 =
          let uu____17364 =
            let uu____17375 =
              let uu____17376 =
                let uu____17381 =
                  let uu____17382 =
                    let uu____17393 =
                      let uu____17398 =
                        let uu____17401 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17401]  in
                      [uu____17398]  in
                    let uu____17406 =
                      let uu____17407 =
                        let uu____17412 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17412, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17407  in
                    (uu____17393, [xx1], uu____17406)  in
                  FStar_SMTEncoding_Util.mkForall uu____17382  in
                (uu____17381, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17376  in
            ([[l_forall_a_b]], [aa; bb], uu____17375)  in
          FStar_SMTEncoding_Util.mkForall uu____17364  in
        (uu____17363, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17356  in
    [uu____17355]  in
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
      let uu____17500 =
        let uu____17507 =
          let uu____17510 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17510]  in
        ("Valid", uu____17507)  in
      FStar_SMTEncoding_Util.mkApp uu____17500  in
    let uu____17513 =
      let uu____17514 =
        let uu____17521 =
          let uu____17522 =
            let uu____17533 =
              let uu____17534 =
                let uu____17539 =
                  let uu____17540 =
                    let uu____17551 =
                      let uu____17556 =
                        let uu____17559 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17559]  in
                      [uu____17556]  in
                    let uu____17564 =
                      let uu____17565 =
                        let uu____17570 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17570, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17565  in
                    (uu____17551, [xx1], uu____17564)  in
                  FStar_SMTEncoding_Util.mkExists uu____17540  in
                (uu____17539, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17534  in
            ([[l_exists_a_b]], [aa; bb], uu____17533)  in
          FStar_SMTEncoding_Util.mkForall uu____17522  in
        (uu____17521, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17514  in
    [uu____17513]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____17636 =
      let uu____17637 =
        let uu____17644 =
          let uu____17645 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____17645 range_ty  in
        let uu____17646 = varops.mk_unique "typing_range_const"  in
        (uu____17644, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____17646)
         in
      FStar_SMTEncoding_Util.mkAssume uu____17637  in
    [uu____17636]  in
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
        let uu____17686 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17686 x1 t  in
      let uu____17687 =
        let uu____17698 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____17698)  in
      FStar_SMTEncoding_Util.mkForall uu____17687  in
    let uu____17721 =
      let uu____17722 =
        let uu____17729 =
          let uu____17730 =
            let uu____17741 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____17741)  in
          FStar_SMTEncoding_Util.mkForall uu____17730  in
        (uu____17729,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17722  in
    [uu____17721]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17797 =
      let uu____17798 =
        let uu____17805 =
          let uu____17806 =
            let uu____17821 =
              let uu____17822 =
                let uu____17827 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17828 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17827, uu____17828)  in
              FStar_SMTEncoding_Util.mkAnd uu____17822  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17821)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17806  in
        (uu____17805,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17798  in
    [uu____17797]  in
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
          let uu____18288 =
            FStar_Util.find_opt
              (fun uu____18320  ->
                 match uu____18320 with
                 | (l,uu____18332) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____18288 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____18366,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____18417 = encode_function_type_as_formula t env  in
        match uu____18417 with
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
              let uu____18469 =
                ((let uu____18472 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____18472) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____18469
              then
                let arg_sorts =
                  let uu____18482 =
                    let uu____18483 = FStar_Syntax_Subst.compress t_norm  in
                    uu____18483.FStar_Syntax_Syntax.n  in
                  match uu____18482 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____18489) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____18519  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____18524 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____18526 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____18526 with
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
                (let uu____18559 = prims.is lid  in
                 if uu____18559
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____18567 = prims.mk lid vname  in
                   match uu____18567 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____18594 =
                      let uu____18605 = curried_arrow_formals_comp t_norm  in
                      match uu____18605 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____18623 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____18623
                            then
                              let uu____18624 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___121_18627 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___121_18627.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___121_18627.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___121_18627.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___121_18627.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___121_18627.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___121_18627.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___121_18627.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___121_18627.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___121_18627.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___121_18627.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___121_18627.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___121_18627.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___121_18627.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___121_18627.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___121_18627.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___121_18627.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___121_18627.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___121_18627.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___121_18627.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___121_18627.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___121_18627.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___121_18627.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___121_18627.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___121_18627.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___121_18627.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___121_18627.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___121_18627.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___121_18627.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___121_18627.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___121_18627.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___121_18627.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___121_18627.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___121_18627.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___121_18627.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___121_18627.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___121_18627.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____18624
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____18639 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____18639)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____18594 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____18689 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____18689 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____18714 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___93_18764  ->
                                       match uu___93_18764 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____18768 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18768 with
                                            | (uu____18789,(xxsym,uu____18791))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____18809 =
                                                  let uu____18810 =
                                                    let uu____18817 =
                                                      let uu____18818 =
                                                        let uu____18829 =
                                                          let uu____18830 =
                                                            let uu____18835 =
                                                              let uu____18836
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____18836
                                                               in
                                                            (vapp,
                                                              uu____18835)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____18830
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18829)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18818
                                                       in
                                                    (uu____18817,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18810
                                                   in
                                                [uu____18809])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____18855 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18855 with
                                            | (uu____18876,(xxsym,uu____18878))
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
                                                let uu____18901 =
                                                  let uu____18902 =
                                                    let uu____18909 =
                                                      let uu____18910 =
                                                        let uu____18921 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18921)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18910
                                                       in
                                                    (uu____18909,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18902
                                                   in
                                                [uu____18901])
                                       | uu____18938 -> []))
                                in
                             let uu____18939 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____18939 with
                              | (vars,guards,env',decls1,uu____18966) ->
                                  let uu____18979 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18988 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18988, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18990 =
                                          encode_formula p env'  in
                                        (match uu____18990 with
                                         | (g,ds) ->
                                             let uu____19001 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____19001,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18979 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____19014 =
                                           let uu____19021 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____19021)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____19014
                                          in
                                       let uu____19030 =
                                         let vname_decl =
                                           let uu____19038 =
                                             let uu____19049 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____19059  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____19049,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____19038
                                            in
                                         let uu____19068 =
                                           let env2 =
                                             let uu___122_19074 = env1  in
                                             {
                                               bindings =
                                                 (uu___122_19074.bindings);
                                               depth = (uu___122_19074.depth);
                                               tcenv = (uu___122_19074.tcenv);
                                               warn = (uu___122_19074.warn);
                                               cache = (uu___122_19074.cache);
                                               nolabels =
                                                 (uu___122_19074.nolabels);
                                               use_zfuel_name =
                                                 (uu___122_19074.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___122_19074.current_module_name)
                                             }  in
                                           let uu____19075 =
                                             let uu____19076 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____19076
                                              in
                                           if uu____19075
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____19068 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____19091::uu____19092 ->
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
                                                     let uu____19132 =
                                                       let uu____19143 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____19143)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____19132
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____19170 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____19173 =
                                               match formals with
                                               | [] ->
                                                   let uu____19190 =
                                                     let uu____19191 =
                                                       let uu____19194 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____19194
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____19191
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____19190)
                                               | uu____19203 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____19210 =
                                                       let uu____19217 =
                                                         let uu____19218 =
                                                           let uu____19229 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____19229)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____19218
                                                          in
                                                       (uu____19217,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____19210
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____19173 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____19030 with
                                        | (decls2,env2) ->
                                            let uu____19272 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____19280 =
                                                encode_term res_t1 env'  in
                                              match uu____19280 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____19293 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____19293, decls)
                                               in
                                            (match uu____19272 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____19304 =
                                                     let uu____19311 =
                                                       let uu____19312 =
                                                         let uu____19323 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____19323)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____19312
                                                        in
                                                     (uu____19311,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____19304
                                                    in
                                                 let freshness =
                                                   let uu____19339 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____19339
                                                   then
                                                     let uu____19344 =
                                                       let uu____19345 =
                                                         let uu____19356 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____19367 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____19356,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____19367)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____19345
                                                        in
                                                     let uu____19370 =
                                                       let uu____19373 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____19373]  in
                                                     uu____19344 ::
                                                       uu____19370
                                                   else []  in
                                                 let g =
                                                   let uu____19378 =
                                                     let uu____19381 =
                                                       let uu____19384 =
                                                         let uu____19387 =
                                                           let uu____19390 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____19390
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____19387
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____19384
                                                        in
                                                     FStar_List.append decls2
                                                       uu____19381
                                                      in
                                                   FStar_List.append decls11
                                                     uu____19378
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
          let uu____19423 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19423 with
          | FStar_Pervasives_Native.None  ->
              let uu____19434 = encode_free_var false env x t t_norm []  in
              (match uu____19434 with
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
            let uu____19497 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____19497 with
            | (decls,env1) ->
                let uu____19516 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____19516
                then
                  let uu____19523 =
                    let uu____19526 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____19526  in
                  (uu____19523, env1)
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
             (fun uu____19584  ->
                fun lb  ->
                  match uu____19584 with
                  | (decls,env1) ->
                      let uu____19604 =
                        let uu____19611 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____19611
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____19604 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____19634 = FStar_Syntax_Util.head_and_args t  in
    match uu____19634 with
    | (hd1,args) ->
        let uu____19671 =
          let uu____19672 = FStar_Syntax_Util.un_uinst hd1  in
          uu____19672.FStar_Syntax_Syntax.n  in
        (match uu____19671 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____19676,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____19695 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____19723  ->
      fun quals  ->
        match uu____19723 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____19807 = FStar_Util.first_N nbinders formals  in
              match uu____19807 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19888  ->
                         fun uu____19889  ->
                           match (uu____19888, uu____19889) with
                           | ((formal,uu____19907),(binder,uu____19909)) ->
                               let uu____19918 =
                                 let uu____19925 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19925)  in
                               FStar_Syntax_Syntax.NT uu____19918) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19933 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19964  ->
                              match uu____19964 with
                              | (x,i) ->
                                  let uu____19975 =
                                    let uu___123_19976 = x  in
                                    let uu____19977 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___123_19976.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___123_19976.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19977
                                    }  in
                                  (uu____19975, i)))
                       in
                    FStar_All.pipe_right uu____19933
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19995 =
                      let uu____20000 = FStar_Syntax_Subst.compress body  in
                      let uu____20001 =
                        let uu____20002 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____20002
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____20000
                        uu____20001
                       in
                    uu____19995 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____20071 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____20071
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___124_20074 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___124_20074.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___124_20074.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___124_20074.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___124_20074.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___124_20074.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___124_20074.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___124_20074.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___124_20074.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___124_20074.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___124_20074.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___124_20074.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___124_20074.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___124_20074.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___124_20074.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___124_20074.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___124_20074.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___124_20074.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___124_20074.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___124_20074.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___124_20074.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___124_20074.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___124_20074.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___124_20074.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___124_20074.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___124_20074.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___124_20074.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___124_20074.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___124_20074.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___124_20074.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___124_20074.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___124_20074.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___124_20074.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___124_20074.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___124_20074.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___124_20074.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___124_20074.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____20111 = FStar_Syntax_Util.abs_formals e  in
                match uu____20111 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____20175::uu____20176 ->
                         let uu____20191 =
                           let uu____20192 =
                             let uu____20195 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____20195
                              in
                           uu____20192.FStar_Syntax_Syntax.n  in
                         (match uu____20191 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____20238 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____20238 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____20280 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____20280
                                   then
                                     let uu____20315 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____20315 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____20409  ->
                                                   fun uu____20410  ->
                                                     match (uu____20409,
                                                             uu____20410)
                                                     with
                                                     | ((x,uu____20428),
                                                        (b,uu____20430)) ->
                                                         let uu____20439 =
                                                           let uu____20446 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____20446)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____20439)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____20448 =
                                            let uu____20469 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____20469)
                                             in
                                          (uu____20448, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____20537 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____20537 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____20626) ->
                              let uu____20631 =
                                let uu____20652 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____20652  in
                              (uu____20631, true)
                          | uu____20717 when Prims.op_Negation norm1 ->
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
                          | uu____20719 ->
                              let uu____20720 =
                                let uu____20721 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____20722 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____20721
                                  uu____20722
                                 in
                              failwith uu____20720)
                     | uu____20747 ->
                         let rec aux' t_norm2 =
                           let uu____20774 =
                             let uu____20775 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____20775.FStar_Syntax_Syntax.n  in
                           match uu____20774 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____20816 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____20816 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____20844 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____20844 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20924)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20929 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20985 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20985
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20997 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____21060  ->
                            fun lb  ->
                              match uu____21060 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____21115 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____21115
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____21118 =
                                      let uu____21127 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____21127
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____21118 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____20997 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____21252 =
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
                        | uu____21258 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____21266 = mk_fv ()  in
                                   mk_Apply uu____21266 vars)
                            else
                              (let uu____21268 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____21268)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____21328;
                             FStar_Syntax_Syntax.lbeff = uu____21329;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____21331;
                             FStar_Syntax_Syntax.lbpos = uu____21332;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____21356 =
                              let uu____21363 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____21363 with
                              | (tcenv',uu____21381,e_t) ->
                                  let uu____21387 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____21398 -> failwith "Impossible"
                                     in
                                  (match uu____21387 with
                                   | (e1,t_norm1) ->
                                       ((let uu___127_21414 = env2  in
                                         {
                                           bindings =
                                             (uu___127_21414.bindings);
                                           depth = (uu___127_21414.depth);
                                           tcenv = tcenv';
                                           warn = (uu___127_21414.warn);
                                           cache = (uu___127_21414.cache);
                                           nolabels =
                                             (uu___127_21414.nolabels);
                                           use_zfuel_name =
                                             (uu___127_21414.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___127_21414.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___127_21414.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____21356 with
                             | (env',e1,t_norm1) ->
                                 let uu____21424 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____21424 with
                                  | ((binders,body,uu____21445,t_body),curry)
                                      ->
                                      ((let uu____21457 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____21457
                                        then
                                          let uu____21458 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____21459 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____21458 uu____21459
                                        else ());
                                       (let uu____21461 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____21461 with
                                        | (vars,guards,env'1,binder_decls,uu____21488)
                                            ->
                                            let body1 =
                                              let uu____21502 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____21502
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
                                              let uu____21519 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____21519 curry fvb
                                                vars
                                               in
                                            let uu____21520 =
                                              let uu____21529 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____21529
                                              then
                                                let uu____21540 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____21541 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____21540, uu____21541)
                                              else
                                                (let uu____21551 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____21551))
                                               in
                                            (match uu____21520 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____21574 =
                                                     let uu____21581 =
                                                       let uu____21582 =
                                                         let uu____21593 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____21593)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____21582
                                                        in
                                                     let uu____21604 =
                                                       let uu____21607 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____21607
                                                        in
                                                     (uu____21581,
                                                       uu____21604,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____21574
                                                    in
                                                 let uu____21610 =
                                                   let uu____21613 =
                                                     let uu____21616 =
                                                       let uu____21619 =
                                                         let uu____21622 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____21622
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____21619
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____21616
                                                      in
                                                   FStar_List.append decls1
                                                     uu____21613
                                                    in
                                                 (uu____21610, env2))))))
                        | uu____21627 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____21690 = varops.fresh "fuel"  in
                          (uu____21690, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21693 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____21740  ->
                                  fun fvb  ->
                                    match uu____21740 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____21786 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21786  in
                                        let gtok =
                                          let uu____21788 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21788  in
                                        let env4 =
                                          let uu____21790 =
                                            let uu____21793 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____21793
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____21790
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____21693 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21901 t_norm
                              uu____21903 =
                              match (uu____21901, uu____21903) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____21933;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____21934;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____21936;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____21937;_})
                                  ->
                                  let uu____21958 =
                                    let uu____21965 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21965 with
                                    | (tcenv',uu____21987,e_t) ->
                                        let uu____21993 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____22004 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21993 with
                                         | (e1,t_norm1) ->
                                             ((let uu___128_22020 = env3  in
                                               {
                                                 bindings =
                                                   (uu___128_22020.bindings);
                                                 depth =
                                                   (uu___128_22020.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___128_22020.warn);
                                                 cache =
                                                   (uu___128_22020.cache);
                                                 nolabels =
                                                   (uu___128_22020.nolabels);
                                                 use_zfuel_name =
                                                   (uu___128_22020.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___128_22020.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___128_22020.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21958 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____22035 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____22035
                                         then
                                           let uu____22036 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____22037 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____22038 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____22036 uu____22037
                                             uu____22038
                                         else ());
                                        (let uu____22040 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____22040 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____22077 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____22077
                                               then
                                                 let uu____22078 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____22079 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____22080 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____22081 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____22078 uu____22079
                                                   uu____22080 uu____22081
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____22085 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____22085 with
                                               | (vars,guards,env'1,binder_decls,uu____22116)
                                                   ->
                                                   let decl_g =
                                                     let uu____22130 =
                                                       let uu____22141 =
                                                         let uu____22144 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____22144
                                                          in
                                                       (g, uu____22141,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____22130
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
                                                     let uu____22169 =
                                                       let uu____22176 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____22176)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22169
                                                      in
                                                   let gsapp =
                                                     let uu____22186 =
                                                       let uu____22193 =
                                                         let uu____22196 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____22196 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22193)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22186
                                                      in
                                                   let gmax =
                                                     let uu____22202 =
                                                       let uu____22209 =
                                                         let uu____22212 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____22212 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____22209)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____22202
                                                      in
                                                   let body1 =
                                                     let uu____22218 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____22218
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____22220 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____22220 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____22238 =
                                                            let uu____22245 =
                                                              let uu____22246
                                                                =
                                                                let uu____22261
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
                                                                  uu____22261)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____22246
                                                               in
                                                            let uu____22282 =
                                                              let uu____22285
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____22285
                                                               in
                                                            (uu____22245,
                                                              uu____22282,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22238
                                                           in
                                                        let eqn_f =
                                                          let uu____22289 =
                                                            let uu____22296 =
                                                              let uu____22297
                                                                =
                                                                let uu____22308
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____22308)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22297
                                                               in
                                                            (uu____22296,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22289
                                                           in
                                                        let eqn_g' =
                                                          let uu____22322 =
                                                            let uu____22329 =
                                                              let uu____22330
                                                                =
                                                                let uu____22341
                                                                  =
                                                                  let uu____22342
                                                                    =
                                                                    let uu____22347
                                                                    =
                                                                    let uu____22348
                                                                    =
                                                                    let uu____22355
                                                                    =
                                                                    let uu____22358
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____22358
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____22355)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____22348
                                                                     in
                                                                    (gsapp,
                                                                    uu____22347)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____22342
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____22341)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____22330
                                                               in
                                                            (uu____22329,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____22322
                                                           in
                                                        let uu____22381 =
                                                          let uu____22390 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____22390
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____22419)
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
                                                                  let uu____22444
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____22444
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____22449
                                                                  =
                                                                  let uu____22456
                                                                    =
                                                                    let uu____22457
                                                                    =
                                                                    let uu____22468
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22468)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22457
                                                                     in
                                                                  (uu____22456,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____22449
                                                                 in
                                                              let uu____22489
                                                                =
                                                                let uu____22496
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____22496
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____22509
                                                                    =
                                                                    let uu____22512
                                                                    =
                                                                    let uu____22513
                                                                    =
                                                                    let uu____22520
                                                                    =
                                                                    let uu____22521
                                                                    =
                                                                    let uu____22532
                                                                    =
                                                                    let uu____22533
                                                                    =
                                                                    let uu____22538
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____22538,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____22533
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22532)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22521
                                                                     in
                                                                    (uu____22520,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____22513
                                                                     in
                                                                    [uu____22512]
                                                                     in
                                                                    (d3,
                                                                    uu____22509)
                                                                 in
                                                              (match uu____22489
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
                                                        (match uu____22381
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
                            let uu____22603 =
                              let uu____22616 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22677  ->
                                   fun uu____22678  ->
                                     match (uu____22677, uu____22678) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22803 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22803 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22616
                               in
                            (match uu____22603 with
                             | (decls2,eqns,env01) ->
                                 let uu____22876 =
                                   let isDeclFun uu___94_22890 =
                                     match uu___94_22890 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22891 -> true
                                     | uu____22902 -> false  in
                                   let uu____22903 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22903
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22876 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22943 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___95_22947  ->
                                 match uu___95_22947 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22948 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22954 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22954)))
                         in
                      if uu____22943
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
                   let uu____23006 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____23006
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
        let uu____23067 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____23067 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____23071 = encode_sigelt' env se  in
      match uu____23071 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____23087 =
                  let uu____23088 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____23088  in
                [uu____23087]
            | uu____23089 ->
                let uu____23090 =
                  let uu____23093 =
                    let uu____23094 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____23094  in
                  uu____23093 :: g  in
                let uu____23095 =
                  let uu____23098 =
                    let uu____23099 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____23099  in
                  [uu____23098]  in
                FStar_List.append uu____23090 uu____23095
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
        let uu____23114 =
          let uu____23115 = FStar_Syntax_Subst.compress t  in
          uu____23115.FStar_Syntax_Syntax.n  in
        match uu____23114 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____23119)) -> s = "opaque_to_smt"
        | uu____23120 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____23127 =
          let uu____23128 = FStar_Syntax_Subst.compress t  in
          uu____23128.FStar_Syntax_Syntax.n  in
        match uu____23127 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____23132)) -> s = "uninterpreted_by_smt"
        | uu____23133 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23138 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____23143 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____23154 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____23157 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____23160 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____23175 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23179 =
            let uu____23180 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____23180 Prims.op_Negation  in
          if uu____23179
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____23208 ->
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
               let uu____23232 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____23232 with
               | (formals,uu____23250) ->
                   let arity = FStar_List.length formals  in
                   let uu____23268 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____23268 with
                    | (aname,atok,env2) ->
                        let uu____23288 =
                          let uu____23293 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____23293 env2  in
                        (match uu____23288 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____23305 =
                                 let uu____23306 =
                                   let uu____23317 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____23333  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____23317,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____23306
                                  in
                               [uu____23305;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____23346 =
                               let aux uu____23402 uu____23403 =
                                 match (uu____23402, uu____23403) with
                                 | ((bv,uu____23455),(env3,acc_sorts,acc)) ->
                                     let uu____23493 = gen_term_var env3 bv
                                        in
                                     (match uu____23493 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____23346 with
                              | (uu____23565,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____23588 =
                                      let uu____23595 =
                                        let uu____23596 =
                                          let uu____23607 =
                                            let uu____23608 =
                                              let uu____23613 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____23613)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23608
                                             in
                                          ([[app]], xs_sorts, uu____23607)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23596
                                         in
                                      (uu____23595,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23588
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23633 =
                                      let uu____23640 =
                                        let uu____23641 =
                                          let uu____23652 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23652)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23641
                                         in
                                      (uu____23640,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23633
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23671 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23671 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23699,uu____23700)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23701 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____23701 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23718,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23724 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___96_23728  ->
                      match uu___96_23728 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23729 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23734 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23735 -> false))
               in
            Prims.op_Negation uu____23724  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23744 =
               let uu____23751 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23751 env fv t quals  in
             match uu____23744 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23766 =
                   let uu____23769 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23769  in
                 (uu____23766, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23777 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23777 with
           | (uu____23786,f1) ->
               let uu____23788 = encode_formula f1 env  in
               (match uu____23788 with
                | (f2,decls) ->
                    let g =
                      let uu____23802 =
                        let uu____23803 =
                          let uu____23810 =
                            let uu____23813 =
                              let uu____23814 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23814
                               in
                            FStar_Pervasives_Native.Some uu____23813  in
                          let uu____23815 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23810, uu____23815)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23803  in
                      [uu____23802]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23821) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23833 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23851 =
                       let uu____23854 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23854.FStar_Syntax_Syntax.fv_name  in
                     uu____23851.FStar_Syntax_Syntax.v  in
                   let uu____23855 =
                     let uu____23856 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23856  in
                   if uu____23855
                   then
                     let val_decl =
                       let uu___131_23884 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___131_23884.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___131_23884.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___131_23884.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23889 = encode_sigelt' env1 val_decl  in
                     match uu____23889 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23833 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23917,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23919;
                          FStar_Syntax_Syntax.lbtyp = uu____23920;
                          FStar_Syntax_Syntax.lbeff = uu____23921;
                          FStar_Syntax_Syntax.lbdef = uu____23922;
                          FStar_Syntax_Syntax.lbattrs = uu____23923;
                          FStar_Syntax_Syntax.lbpos = uu____23924;_}::[]),uu____23925)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23948 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____23948 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23977 =
                   let uu____23980 =
                     let uu____23981 =
                       let uu____23988 =
                         let uu____23989 =
                           let uu____24000 =
                             let uu____24001 =
                               let uu____24006 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____24006)  in
                             FStar_SMTEncoding_Util.mkEq uu____24001  in
                           ([[b2t_x]], [xx], uu____24000)  in
                         FStar_SMTEncoding_Util.mkForall uu____23989  in
                       (uu____23988,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23981  in
                   [uu____23980]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23977
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____24039,uu____24040) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_24049  ->
                  match uu___97_24049 with
                  | FStar_Syntax_Syntax.Discriminator uu____24050 -> true
                  | uu____24051 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____24054,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____24065 =
                     let uu____24066 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____24066.FStar_Ident.idText  in
                   uu____24065 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___98_24070  ->
                     match uu___98_24070 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____24071 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____24075) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___99_24092  ->
                  match uu___99_24092 with
                  | FStar_Syntax_Syntax.Projector uu____24093 -> true
                  | uu____24098 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____24101 = try_lookup_free_var env l  in
          (match uu____24101 with
           | FStar_Pervasives_Native.Some uu____24108 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___132_24112 = se  in
                 let uu____24113 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____24113;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___132_24112.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___132_24112.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___132_24112.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____24120) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____24138) ->
          let uu____24147 = encode_sigelts env ses  in
          (match uu____24147 with
           | (g,env1) ->
               let uu____24164 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___100_24187  ->
                         match uu___100_24187 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____24188;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____24189;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____24190;_}
                             -> false
                         | uu____24193 -> true))
                  in
               (match uu____24164 with
                | (g',inversions) ->
                    let uu____24208 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___101_24229  ->
                              match uu___101_24229 with
                              | FStar_SMTEncoding_Term.DeclFun uu____24230 ->
                                  true
                              | uu____24241 -> false))
                       in
                    (match uu____24208 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____24259,tps,k,uu____24262,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___102_24279  ->
                    match uu___102_24279 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____24280 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____24291 = c  in
              match uu____24291 with
              | (name,args,uu____24296,uu____24297,uu____24298) ->
                  let uu____24303 =
                    let uu____24304 =
                      let uu____24315 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____24332  ->
                                match uu____24332 with
                                | (uu____24339,sort,uu____24341) -> sort))
                         in
                      (name, uu____24315, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____24304  in
                  [uu____24303]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____24372 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____24378 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____24378 FStar_Option.isNone))
               in
            if uu____24372
            then []
            else
              (let uu____24410 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____24410 with
               | (xxsym,xx) ->
                   let uu____24419 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____24458  ->
                             fun l  ->
                               match uu____24458 with
                               | (out,decls) ->
                                   let uu____24478 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____24478 with
                                    | (uu____24489,data_t) ->
                                        let uu____24491 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____24491 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____24537 =
                                                 let uu____24538 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____24538.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____24537 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____24549,indices) ->
                                                   indices
                                               | uu____24571 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24595  ->
                                                         match uu____24595
                                                         with
                                                         | (x,uu____24601) ->
                                                             let uu____24602
                                                               =
                                                               let uu____24603
                                                                 =
                                                                 let uu____24610
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____24610,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24603
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____24602)
                                                    env)
                                                in
                                             let uu____24613 =
                                               encode_args indices env1  in
                                             (match uu____24613 with
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
                                                      let uu____24639 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____24655
                                                                 =
                                                                 let uu____24660
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____24660,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____24655)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____24639
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____24663 =
                                                      let uu____24664 =
                                                        let uu____24669 =
                                                          let uu____24670 =
                                                            let uu____24675 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____24675,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____24670
                                                           in
                                                        (out, uu____24669)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____24664
                                                       in
                                                    (uu____24663,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____24419 with
                    | (data_ax,decls) ->
                        let uu____24688 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____24688 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24699 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24699 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____24703 =
                                 let uu____24710 =
                                   let uu____24711 =
                                     let uu____24722 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24737 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24722,
                                       uu____24737)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24711
                                    in
                                 let uu____24752 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____24710,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24752)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____24703
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24755 =
            let uu____24768 =
              let uu____24769 = FStar_Syntax_Subst.compress k  in
              uu____24769.FStar_Syntax_Syntax.n  in
            match uu____24768 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24814 -> (tps, k)  in
          (match uu____24755 with
           | (formals,res) ->
               let uu____24837 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24837 with
                | (formals1,res1) ->
                    let uu____24848 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24848 with
                     | (vars,guards,env',binder_decls,uu____24873) ->
                         let arity = FStar_List.length vars  in
                         let uu____24887 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____24887 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24910 =
                                  let uu____24917 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24917)  in
                                FStar_SMTEncoding_Util.mkApp uu____24910  in
                              let uu____24926 =
                                let tname_decl =
                                  let uu____24936 =
                                    let uu____24937 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24969  ->
                                              match uu____24969 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24982 = varops.next_id ()  in
                                    (tname, uu____24937,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24982, false)
                                     in
                                  constructor_or_logic_type_decl uu____24936
                                   in
                                let uu____24991 =
                                  match vars with
                                  | [] ->
                                      let uu____25004 =
                                        let uu____25005 =
                                          let uu____25008 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____25008
                                           in
                                        push_free_var env1 t arity tname
                                          uu____25005
                                         in
                                      ([], uu____25004)
                                  | uu____25019 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____25028 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____25028
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____25042 =
                                          let uu____25049 =
                                            let uu____25050 =
                                              let uu____25065 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____25065)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____25050
                                             in
                                          (uu____25049,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____25042
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24991 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24926 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____25105 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____25105 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____25123 =
                                               let uu____25124 =
                                                 let uu____25131 =
                                                   let uu____25132 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____25132
                                                    in
                                                 (uu____25131,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____25124
                                                in
                                             [uu____25123]
                                           else []  in
                                         let uu____25136 =
                                           let uu____25139 =
                                             let uu____25142 =
                                               let uu____25143 =
                                                 let uu____25150 =
                                                   let uu____25151 =
                                                     let uu____25162 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____25162)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____25151
                                                    in
                                                 (uu____25150,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____25143
                                                in
                                             [uu____25142]  in
                                           FStar_List.append karr uu____25139
                                            in
                                         FStar_List.append decls1 uu____25136
                                      in
                                   let aux =
                                     let uu____25178 =
                                       let uu____25181 =
                                         inversion_axioms tapp vars  in
                                       let uu____25184 =
                                         let uu____25187 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____25187]  in
                                       FStar_List.append uu____25181
                                         uu____25184
                                        in
                                     FStar_List.append kindingAx uu____25178
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____25194,uu____25195,uu____25196,uu____25197,uu____25198)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____25206,t,uu____25208,n_tps,uu____25210) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____25218 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____25218 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____25258 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____25258 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____25279 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____25279 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____25293 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____25293 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____25363 =
                                            mk_term_projector_name d x  in
                                          (uu____25363,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____25365 =
                                  let uu____25384 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____25384, true)
                                   in
                                FStar_All.pipe_right uu____25365
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
                              let uu____25423 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____25423 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____25435::uu____25436 ->
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
                                         let uu____25481 =
                                           let uu____25492 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____25492)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____25481
                                     | uu____25517 -> tok_typing  in
                                   let uu____25526 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____25526 with
                                    | (vars',guards',env'',decls_formals,uu____25551)
                                        ->
                                        let uu____25564 =
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
                                        (match uu____25564 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25595 ->
                                                   let uu____25602 =
                                                     let uu____25603 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25603
                                                      in
                                                   [uu____25602]
                                                in
                                             let encode_elim uu____25615 =
                                               let uu____25616 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____25616 with
                                               | (head1,args) ->
                                                   let uu____25659 =
                                                     let uu____25660 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____25660.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____25659 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25670;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25671;_},uu____25672)
                                                        ->
                                                        let uu____25677 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25677
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25690
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25690
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
                                                                    uu____25739
                                                                    ->
                                                                    let uu____25740
                                                                    =
                                                                    let uu____25745
                                                                    =
                                                                    let uu____25746
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25746
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25745)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25740
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25762
                                                                    =
                                                                    let uu____25763
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25763
                                                                     in
                                                                    if
                                                                    uu____25762
                                                                    then
                                                                    let uu____25776
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25776]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25778
                                                                    =
                                                                    let uu____25791
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25841
                                                                     ->
                                                                    fun
                                                                    uu____25842
                                                                     ->
                                                                    match 
                                                                    (uu____25841,
                                                                    uu____25842)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25937
                                                                    =
                                                                    let uu____25944
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25944
                                                                     in
                                                                    (match uu____25937
                                                                    with
                                                                    | 
                                                                    (uu____25957,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25965
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25965
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25967
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25967
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
                                                                    uu____25791
                                                                     in
                                                                  (match uu____25778
                                                                   with
                                                                   | 
                                                                   (uu____25982,arg_vars,elim_eqns_or_guards,uu____25985)
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
                                                                    let uu____26013
                                                                    =
                                                                    let uu____26020
                                                                    =
                                                                    let uu____26021
                                                                    =
                                                                    let uu____26032
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26043
                                                                    =
                                                                    let uu____26044
                                                                    =
                                                                    let uu____26049
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26049)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26044
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26032,
                                                                    uu____26043)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26021
                                                                     in
                                                                    (uu____26020,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26013
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26067
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26067
                                                                    then
                                                                    let x =
                                                                    let uu____26073
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26073,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26075
                                                                    =
                                                                    let uu____26082
                                                                    =
                                                                    let uu____26083
                                                                    =
                                                                    let uu____26094
                                                                    =
                                                                    let uu____26099
                                                                    =
                                                                    let uu____26102
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26102]
                                                                     in
                                                                    [uu____26099]
                                                                     in
                                                                    let uu____26107
                                                                    =
                                                                    let uu____26108
                                                                    =
                                                                    let uu____26113
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26114
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26113,
                                                                    uu____26114)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26108
                                                                     in
                                                                    (uu____26094,
                                                                    [x],
                                                                    uu____26107)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26083
                                                                     in
                                                                    let uu____26133
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26082,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26133)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26075
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26140
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
                                                                    (let uu____26168
                                                                    =
                                                                    let uu____26169
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26169
                                                                    dapp1  in
                                                                    [uu____26168])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26140
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26176
                                                                    =
                                                                    let uu____26183
                                                                    =
                                                                    let uu____26184
                                                                    =
                                                                    let uu____26195
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26206
                                                                    =
                                                                    let uu____26207
                                                                    =
                                                                    let uu____26212
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26212)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26207
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26195,
                                                                    uu____26206)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26184
                                                                     in
                                                                    (uu____26183,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26176)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____26232 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____26232
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____26245
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____26245
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
                                                                    uu____26294
                                                                    ->
                                                                    let uu____26295
                                                                    =
                                                                    let uu____26300
                                                                    =
                                                                    let uu____26301
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____26301
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____26300)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____26295
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____26317
                                                                    =
                                                                    let uu____26318
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____26318
                                                                     in
                                                                    if
                                                                    uu____26317
                                                                    then
                                                                    let uu____26331
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____26331]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____26333
                                                                    =
                                                                    let uu____26346
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____26396
                                                                     ->
                                                                    fun
                                                                    uu____26397
                                                                     ->
                                                                    match 
                                                                    (uu____26396,
                                                                    uu____26397)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____26492
                                                                    =
                                                                    let uu____26499
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____26499
                                                                     in
                                                                    (match uu____26492
                                                                    with
                                                                    | 
                                                                    (uu____26512,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____26520
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____26520
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____26522
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____26522
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
                                                                    uu____26346
                                                                     in
                                                                  (match uu____26333
                                                                   with
                                                                   | 
                                                                   (uu____26537,arg_vars,elim_eqns_or_guards,uu____26540)
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
                                                                    let uu____26568
                                                                    =
                                                                    let uu____26575
                                                                    =
                                                                    let uu____26576
                                                                    =
                                                                    let uu____26587
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26598
                                                                    =
                                                                    let uu____26599
                                                                    =
                                                                    let uu____26604
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26604)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26599
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26587,
                                                                    uu____26598)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26576
                                                                     in
                                                                    (uu____26575,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26568
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26622
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26622
                                                                    then
                                                                    let x =
                                                                    let uu____26628
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26628,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26630
                                                                    =
                                                                    let uu____26637
                                                                    =
                                                                    let uu____26638
                                                                    =
                                                                    let uu____26649
                                                                    =
                                                                    let uu____26654
                                                                    =
                                                                    let uu____26657
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26657]
                                                                     in
                                                                    [uu____26654]
                                                                     in
                                                                    let uu____26662
                                                                    =
                                                                    let uu____26663
                                                                    =
                                                                    let uu____26668
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26669
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26668,
                                                                    uu____26669)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26663
                                                                     in
                                                                    (uu____26649,
                                                                    [x],
                                                                    uu____26662)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26638
                                                                     in
                                                                    let uu____26688
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26637,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26688)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26630
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26695
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
                                                                    (let uu____26723
                                                                    =
                                                                    let uu____26724
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26724
                                                                    dapp1  in
                                                                    [uu____26723])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26695
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26731
                                                                    =
                                                                    let uu____26738
                                                                    =
                                                                    let uu____26739
                                                                    =
                                                                    let uu____26750
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26761
                                                                    =
                                                                    let uu____26762
                                                                    =
                                                                    let uu____26767
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26767)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26762
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26750,
                                                                    uu____26761)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26739
                                                                     in
                                                                    (uu____26738,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26731)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____26786 ->
                                                        ((let uu____26788 =
                                                            let uu____26793 =
                                                              let uu____26794
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____26795
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____26794
                                                                uu____26795
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____26793)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26788);
                                                         ([], [])))
                                                in
                                             let uu____26800 = encode_elim ()
                                                in
                                             (match uu____26800 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26820 =
                                                      let uu____26823 =
                                                        let uu____26826 =
                                                          let uu____26829 =
                                                            let uu____26832 =
                                                              let uu____26833
                                                                =
                                                                let uu____26844
                                                                  =
                                                                  let uu____26847
                                                                    =
                                                                    let uu____26848
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26848
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26847
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26844)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26833
                                                               in
                                                            [uu____26832]  in
                                                          let uu____26853 =
                                                            let uu____26856 =
                                                              let uu____26859
                                                                =
                                                                let uu____26862
                                                                  =
                                                                  let uu____26865
                                                                    =
                                                                    let uu____26868
                                                                    =
                                                                    let uu____26871
                                                                    =
                                                                    let uu____26872
                                                                    =
                                                                    let uu____26879
                                                                    =
                                                                    let uu____26880
                                                                    =
                                                                    let uu____26891
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26891)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26880
                                                                     in
                                                                    (uu____26879,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26872
                                                                     in
                                                                    let uu____26904
                                                                    =
                                                                    let uu____26907
                                                                    =
                                                                    let uu____26908
                                                                    =
                                                                    let uu____26915
                                                                    =
                                                                    let uu____26916
                                                                    =
                                                                    let uu____26927
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____26938
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26927,
                                                                    uu____26938)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26916
                                                                     in
                                                                    (uu____26915,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26908
                                                                     in
                                                                    [uu____26907]
                                                                     in
                                                                    uu____26871
                                                                    ::
                                                                    uu____26904
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26868
                                                                     in
                                                                  FStar_List.append
                                                                    uu____26865
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26862
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26859
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26856
                                                             in
                                                          FStar_List.append
                                                            uu____26829
                                                            uu____26853
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____26826
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____26823
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26820
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
           (fun uu____26984  ->
              fun se  ->
                match uu____26984 with
                | (g,env1) ->
                    let uu____27004 = encode_sigelt env1 se  in
                    (match uu____27004 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____27069 =
        match uu____27069 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____27101 ->
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
                 ((let uu____27107 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____27107
                   then
                     let uu____27108 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____27109 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____27110 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____27108 uu____27109 uu____27110
                   else ());
                  (let uu____27112 = encode_term t1 env1  in
                   match uu____27112 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____27128 =
                         let uu____27135 =
                           let uu____27136 =
                             let uu____27137 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____27137
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____27136  in
                         new_term_constant_from_string env1 x uu____27135  in
                       (match uu____27128 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____27153 = FStar_Options.log_queries ()
                                 in
                              if uu____27153
                              then
                                let uu____27156 =
                                  let uu____27157 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____27158 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____27159 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____27157 uu____27158 uu____27159
                                   in
                                FStar_Pervasives_Native.Some uu____27156
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____27175,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____27189 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____27189 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____27212,se,uu____27214) ->
                 let uu____27219 = encode_sigelt env1 se  in
                 (match uu____27219 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____27236,se) ->
                 let uu____27242 = encode_sigelt env1 se  in
                 (match uu____27242 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____27259 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____27259 with | (uu____27282,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____27297 'Auu____27298 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____27297,'Auu____27298)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____27367  ->
              match uu____27367 with
              | (l,uu____27379,uu____27380) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____27426  ->
              match uu____27426 with
              | (l,uu____27440,uu____27441) ->
                  let uu____27450 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____27451 =
                    let uu____27454 =
                      let uu____27455 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____27455  in
                    [uu____27454]  in
                  uu____27450 :: uu____27451))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____27482 =
      let uu____27485 =
        let uu____27486 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____27489 =
          let uu____27490 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____27490 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____27486;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____27489
        }  in
      [uu____27485]  in
    FStar_ST.op_Colon_Equals last_env uu____27482
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____27528 = FStar_ST.op_Bang last_env  in
      match uu____27528 with
      | [] -> failwith "No env; call init first!"
      | e::uu____27559 ->
          let uu___133_27562 = e  in
          let uu____27563 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___133_27562.bindings);
            depth = (uu___133_27562.depth);
            tcenv;
            warn = (uu___133_27562.warn);
            cache = (uu___133_27562.cache);
            nolabels = (uu___133_27562.nolabels);
            use_zfuel_name = (uu___133_27562.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_27562.encode_non_total_function_typ);
            current_module_name = uu____27563
          }
  
let (set_env : env_t -> unit) =
  fun env  ->
    let uu____27569 = FStar_ST.op_Bang last_env  in
    match uu____27569 with
    | [] -> failwith "Empty env stack"
    | uu____27599::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____27634  ->
    let uu____27635 = FStar_ST.op_Bang last_env  in
    match uu____27635 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___134_27673 = hd1  in
          {
            bindings = (uu___134_27673.bindings);
            depth = (uu___134_27673.depth);
            tcenv = (uu___134_27673.tcenv);
            warn = (uu___134_27673.warn);
            cache = refs;
            nolabels = (uu___134_27673.nolabels);
            use_zfuel_name = (uu___134_27673.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_27673.encode_non_total_function_typ);
            current_module_name = (uu___134_27673.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____27705  ->
    let uu____27706 = FStar_ST.op_Bang last_env  in
    match uu____27706 with
    | [] -> failwith "Popping an empty stack"
    | uu____27736::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____27818::uu____27819,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___135_27827 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___135_27827.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___135_27827.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___135_27827.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27828 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____27847 =
        let uu____27850 =
          let uu____27851 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27851  in
        let uu____27852 = open_fact_db_tags env  in uu____27850 ::
          uu____27852
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27847
  
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
      let uu____27878 = encode_sigelt env se  in
      match uu____27878 with
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
        let uu____27920 = FStar_Options.log_queries ()  in
        if uu____27920
        then
          let uu____27923 =
            let uu____27924 =
              let uu____27925 =
                let uu____27926 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27926 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27925  in
            FStar_SMTEncoding_Term.Caption uu____27924  in
          uu____27923 :: decls
        else decls  in
      (let uu____27937 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27937
       then
         let uu____27938 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27938
       else ());
      (let env =
         let uu____27941 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____27941 tcenv  in
       let uu____27942 = encode_top_level_facts env se  in
       match uu____27942 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27956 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____27956)))
  
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
      (let uu____27972 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27972
       then
         let uu____27973 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27973
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____28012  ->
                 fun se  ->
                   match uu____28012 with
                   | (g,env2) ->
                       let uu____28032 = encode_top_level_facts env2 se  in
                       (match uu____28032 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____28055 =
         encode_signature
           (let uu___136_28064 = env  in
            {
              bindings = (uu___136_28064.bindings);
              depth = (uu___136_28064.depth);
              tcenv = (uu___136_28064.tcenv);
              warn = false;
              cache = (uu___136_28064.cache);
              nolabels = (uu___136_28064.nolabels);
              use_zfuel_name = (uu___136_28064.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___136_28064.encode_non_total_function_typ);
              current_module_name = (uu___136_28064.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____28055 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____28083 = FStar_Options.log_queries ()  in
             if uu____28083
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___137_28091 = env1  in
               {
                 bindings = (uu___137_28091.bindings);
                 depth = (uu___137_28091.depth);
                 tcenv = (uu___137_28091.tcenv);
                 warn = true;
                 cache = (uu___137_28091.cache);
                 nolabels = (uu___137_28091.nolabels);
                 use_zfuel_name = (uu___137_28091.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___137_28091.encode_non_total_function_typ);
                 current_module_name = (uu___137_28091.current_module_name)
               });
            (let uu____28093 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____28093
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
        (let uu____28151 =
           let uu____28152 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____28152.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____28151);
        (let env =
           let uu____28154 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____28154 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____28166 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____28203 = aux rest  in
                 (match uu____28203 with
                  | (out,rest1) ->
                      let t =
                        let uu____28233 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____28233 with
                        | FStar_Pervasives_Native.Some uu____28238 ->
                            let uu____28239 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____28239
                              x.FStar_Syntax_Syntax.sort
                        | uu____28240 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____28244 =
                        let uu____28247 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___138_28250 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___138_28250.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___138_28250.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____28247 :: out  in
                      (uu____28244, rest1))
             | uu____28255 -> ([], bindings1)  in
           let uu____28262 = aux bindings  in
           match uu____28262 with
           | (closing,bindings1) ->
               let uu____28287 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____28287, bindings1)
            in
         match uu____28166 with
         | (q1,bindings1) ->
             let uu____28310 =
               let uu____28315 =
                 FStar_List.filter
                   (fun uu___103_28320  ->
                      match uu___103_28320 with
                      | FStar_TypeChecker_Env.Binding_sig uu____28321 ->
                          false
                      | uu____28328 -> true) bindings1
                  in
               encode_env_bindings env uu____28315  in
             (match uu____28310 with
              | (env_decls,env1) ->
                  ((let uu____28346 =
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
                    if uu____28346
                    then
                      let uu____28347 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____28347
                    else ());
                   (let uu____28349 = encode_formula q1 env1  in
                    match uu____28349 with
                    | (phi,qdecls) ->
                        let uu____28370 =
                          let uu____28375 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____28375 phi
                           in
                        (match uu____28370 with
                         | (labels,phi1) ->
                             let uu____28392 = encode_labels labels  in
                             (match uu____28392 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____28429 =
                                      let uu____28436 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____28437 =
                                        varops.mk_unique "@query"  in
                                      (uu____28436,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____28437)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____28429
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
  