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
        let fail1 uu____188 =
          let uu____189 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____189  in
        let uu____190 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____190 with
        | (uu____195,t) ->
            let uu____197 =
              let uu____198 = FStar_Syntax_Subst.compress t  in
              uu____198.FStar_Syntax_Syntax.n  in
            (match uu____197 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____219 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____219 with
                  | (binders,uu____225) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____240 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____251 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____251
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____262 =
        let uu____267 = mk_term_projector_name lid a  in
        (uu____267,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____262
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____278 =
        let uu____283 = mk_term_projector_name_by_pos lid i  in
        (uu____283,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____278
  
let mk_data_tester :
  'Auu____292 .
    'Auu____292 ->
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
  let new_scope uu____775 =
    let uu____776 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____779 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____776, uu____779)  in
  let scopes =
    let uu____799 = let uu____810 = new_scope ()  in [uu____810]  in
    FStar_Util.mk_ref uu____799  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____852 =
        let uu____855 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____855
          (fun uu____942  ->
             match uu____942 with
             | (names1,uu____954) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____852 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____963 ->
          let uu____964 = FStar_Util.incr ctr  in
          let uu____998 =
            let uu____999 =
              let uu____1000 = FStar_ST.op_Bang ctr  in
              Prims.string_of_int uu____1000  in
            Prims.strcat "__" uu____999  in
          Prims.strcat y1 uu____998
       in
    let top_scope =
      let uu____1049 =
        let uu____1058 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1058
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1049  in
    let uu____1156 = FStar_Util.smap_add top_scope y2 true  in y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1175 =
    let uu____1176 = FStar_Util.incr ctr  in FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1260 =
      let uu____1261 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1261  in
    FStar_Util.format2 "%s_%s" pfx uu____1260  in
  let string_const s =
    let uu____1267 =
      let uu____1270 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1270
        (fun uu____1357  ->
           match uu____1357 with
           | (uu____1368,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1267 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1381 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1381  in
        let top_scope =
          let uu____1385 =
            let uu____1394 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1394  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1385  in
        let uu____1492 = FStar_Util.smap_add top_scope s f  in f
     in
  let push1 uu____1497 =
    let uu____1498 =
      let uu____1509 = new_scope ()  in
      let uu____1518 = FStar_ST.op_Bang scopes  in uu____1509 :: uu____1518
       in
    FStar_ST.op_Colon_Equals scopes uu____1498  in
  let pop1 uu____1671 =
    let uu____1672 =
      let uu____1683 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1683
       in
    FStar_ST.op_Colon_Equals scopes uu____1672  in
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
    let uu___105_1837 = x  in
    let uu____1838 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1838;
      FStar_Syntax_Syntax.index = (uu___105_1837.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___105_1837.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1963 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1989 -> false
  
let (__proj__Binding_fvar__item___0 : binding -> fvar_binding) =
  fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____2003 'Auu____2004 .
    'Auu____2003 ->
      ('Auu____2003,'Auu____2004 FStar_Pervasives_Native.option)
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
  'Auu____2332 .
    'Auu____2332 ->
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
                 (fun uu___82_2370  ->
                    match uu___82_2370 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2374 -> []))
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
    let uu____2387 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___83_2397  ->
              match uu___83_2397 with
              | Binding_var (x,uu____2399) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid))
       in
    FStar_All.pipe_right uu____2387 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2409 .
    env_t ->
      (binding -> 'Auu____2409 FStar_Pervasives_Native.option) ->
        'Auu____2409 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2443 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2443
      then
        let uu____2446 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2446
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
      let uu____2463 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2463)
  
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
        (let uu___106_2483 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___106_2483.tcenv);
           warn = (uu___106_2483.warn);
           cache = (uu___106_2483.cache);
           nolabels = (uu___106_2483.nolabels);
           use_zfuel_name = (uu___106_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___106_2483.encode_non_total_function_typ);
           current_module_name = (uu___106_2483.current_module_name)
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
        (let uu___107_2505 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___107_2505.depth);
           tcenv = (uu___107_2505.tcenv);
           warn = (uu___107_2505.warn);
           cache = (uu___107_2505.cache);
           nolabels = (uu___107_2505.nolabels);
           use_zfuel_name = (uu___107_2505.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___107_2505.encode_non_total_function_typ);
           current_module_name = (uu___107_2505.current_module_name)
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
          (let uu___108_2532 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___108_2532.depth);
             tcenv = (uu___108_2532.tcenv);
             warn = (uu___108_2532.warn);
             cache = (uu___108_2532.cache);
             nolabels = (uu___108_2532.nolabels);
             use_zfuel_name = (uu___108_2532.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___108_2532.encode_non_total_function_typ);
             current_module_name = (uu___108_2532.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___109_2548 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___109_2548.depth);
          tcenv = (uu___109_2548.tcenv);
          warn = (uu___109_2548.warn);
          cache = (uu___109_2548.cache);
          nolabels = (uu___109_2548.nolabels);
          use_zfuel_name = (uu___109_2548.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___109_2548.encode_non_total_function_typ);
          current_module_name = (uu___109_2548.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___84_2577  ->
             match uu___84_2577 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2590 -> FStar_Pervasives_Native.None)
         in
      let uu____2595 = aux a  in
      match uu____2595 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2607 = aux a2  in
          (match uu____2607 with
           | FStar_Pervasives_Native.None  ->
               let uu____2618 =
                 let uu____2619 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2620 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2619 uu____2620
                  in
               failwith uu____2618
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
          (let uu___110_2694 = env  in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___110_2694.depth);
             tcenv = (uu___110_2694.tcenv);
             warn = (uu___110_2694.warn);
             cache = (uu___110_2694.cache);
             nolabels = (uu___110_2694.nolabels);
             use_zfuel_name = (uu___110_2694.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___110_2694.encode_non_total_function_typ);
             current_module_name = (uu___110_2694.current_module_name)
           }))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___85_2709  ->
           match uu___85_2709 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2713 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2724 =
        lookup_binding env
          (fun uu___86_2729  ->
             match uu___86_2729 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2733 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2724 FStar_Option.isSome
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2746 = try_lookup_lid env a  in
      match uu____2746 with
      | FStar_Pervasives_Native.None  ->
          let uu____2749 =
            let uu____2750 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2750  in
          failwith uu____2749
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
            let uu___111_2782 = env  in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___111_2782.depth);
              tcenv = (uu___111_2782.tcenv);
              warn = (uu___111_2782.warn);
              cache = (uu___111_2782.cache);
              nolabels = (uu___111_2782.nolabels);
              use_zfuel_name = (uu___111_2782.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___111_2782.encode_non_total_function_typ);
              current_module_name = (uu___111_2782.current_module_name)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2800 =
            let uu____2807 =
              let uu____2810 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2810]  in
            (f, uu____2807)  in
          FStar_SMTEncoding_Util.mkApp uu____2800  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___112_2816 = env  in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___112_2816.depth);
          tcenv = (uu___112_2816.tcenv);
          warn = (uu___112_2816.warn);
          cache = (uu___112_2816.cache);
          nolabels = (uu___112_2816.nolabels);
          use_zfuel_name = (uu___112_2816.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___112_2816.encode_non_total_function_typ);
          current_module_name = (uu___112_2816.current_module_name)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2829 = try_lookup_lid env l  in
      match uu____2829 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2838 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2846,fuel::[]) ->
                         let uu____2850 =
                           let uu____2851 =
                             let uu____2852 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2852
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2851 "fuel"  in
                         if uu____2850
                         then
                           let uu____2855 =
                             let uu____2856 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2856
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_17  ->
                                FStar_Pervasives_Native.Some _0_17)
                             uu____2855
                         else FStar_Pervasives_Native.Some t
                     | uu____2860 -> FStar_Pervasives_Native.Some t)
                | uu____2861 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2878 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2878 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2882 =
            let uu____2883 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2883  in
          failwith uu____2882
  
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
            FStar_SMTEncoding_Term.freevars = uu____2936;
            FStar_SMTEncoding_Term.rng = uu____2937;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____2952 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____2980 ->
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
        (fun uu___87_2997  ->
           match uu___87_2997 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____3001 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3008 .
    'Auu____3008 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3028  ->
      match uu____3028 with
      | (pats,vars,body) ->
          let fallback uu____3054 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3059 = FStar_Options.unthrottle_inductives ()  in
          if uu____3059
          then fallback ()
          else
            (let uu____3061 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3061 with
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
                           | uu____3093 -> p))
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
                             let uu____3114 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3114
                         | uu____3117 ->
                             let uu____3118 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3118 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3123 -> body  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3170 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3183 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3190 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3191 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3208 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3225 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3227 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3227 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3245;
             FStar_Syntax_Syntax.vars = uu____3246;_},uu____3247)
          ->
          let uu____3268 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3268 FStar_Option.isNone
      | uu____3285 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____3296 =
        let uu____3297 = FStar_Syntax_Util.un_uinst t  in
        uu____3297.FStar_Syntax_Syntax.n  in
      match uu____3296 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3300,uu____3301,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___88_3322  ->
                  match uu___88_3322 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3323 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3325 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3325 FStar_Option.isSome
      | uu____3342 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____3353 = head_normal env t  in
      if uu____3353
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
    let uu____3370 =
      let uu____3371 = FStar_Syntax_Syntax.null_binder t  in [uu____3371]  in
    let uu____3372 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3370 uu____3372 FStar_Pervasives_Native.None
  
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
                    let uu____3414 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3414
                | s ->
                    let uu____3416 = ()  in
                    let uu____3417 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3417) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'Auu____3444 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3444
  =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____3465 =
            let uu____3470 =
              let uu____3471 = FStar_Util.string_of_int arity  in
              let uu____3472 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3471 uu____3472
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3470)  in
          FStar_Errors.raise_error uu____3465 rng
  
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
              (let uu____3511 = FStar_Util.first_N arity args  in
               match uu____3511 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3534 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3534 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___89_3543  ->
    match uu___89_3543 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3544 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____3588;
                       FStar_SMTEncoding_Term.rng = uu____3589;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3612) ->
              let uu____3621 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3632 -> false) args (FStar_List.rev xs))
                 in
              if uu____3621
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3636,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3640 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3644 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3644))
                 in
              if uu____3640
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3648 -> FStar_Pervasives_Native.None  in
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
    | uu____3901 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3907 -> false
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3932 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3945 ->
            let uu____3952 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3952
        | uu____3953 ->
            if norm1
            then let uu____3954 = whnf env t1  in aux false uu____3954
            else
              (let uu____3956 =
                 let uu____3957 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3958 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3957 uu____3958
                  in
               failwith uu____3956)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3992) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3997 ->
        let uu____3998 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3998)
  
let is_arithmetic_primitive :
  'Auu____4015 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4015 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4037::uu____4038::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4042::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4045 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4068 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4085 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4092 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4092)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4133)::uu____4134::uu____4135::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4186)::uu____4187::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4224 -> false
  
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
          let uu____4527 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4527, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4530 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4530, [])
      | FStar_Const.Const_char c1 ->
          let uu____4534 =
            let uu____4535 =
              let uu____4542 =
                let uu____4545 =
                  let uu____4546 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4546  in
                [uu____4545]  in
              ("FStar.Char.__char_of_int", uu____4542)  in
            FStar_SMTEncoding_Util.mkApp uu____4535  in
          (uu____4534, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4562 =
            let uu____4563 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4563  in
          (uu____4562, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4584) ->
          let uu____4585 = varops.string_const s  in (uu____4585, [])
      | FStar_Const.Const_range uu____4588 ->
          let uu____4589 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4589, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4595 =
            let uu____4596 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4596  in
          failwith uu____4595

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
        let uu____4624 =
          let uu____4625 =
            FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
          if uu____4625
          then
            let uu____4626 = FStar_Syntax_Print.binders_to_string ", " bs  in
            FStar_Util.print1 "Encoding binders %s\n" uu____4626
          else ()  in
        let uu____4628 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4712  ->
                  fun b  ->
                    match uu____4712 with
                    | (vars,guards,env1,decls,names1) ->
                        let uu____4791 =
                          let x = unmangle (FStar_Pervasives_Native.fst b)
                             in
                          let uu____4807 = gen_term_var env1 x  in
                          match uu____4807 with
                          | (xxsym,xx,env') ->
                              let uu____4831 =
                                let uu____4836 =
                                  norm env1 x.FStar_Syntax_Syntax.sort  in
                                encode_term_pred fuel_opt uu____4836 env1 xx
                                 in
                              (match uu____4831 with
                               | (guard_x_t,decls') ->
                                   ((xxsym, FStar_SMTEncoding_Term.Term_sort),
                                     guard_x_t, env', decls', x))
                           in
                        (match uu____4791 with
                         | (v1,g,env2,decls',n1) ->
                             ((v1 :: vars), (g :: guards), env2,
                               (FStar_List.append decls decls'), (n1 ::
                               names1)))) ([], [], env, [], []))
           in
        match uu____4628 with
        | (vars,guards,env1,decls,names1) ->
            ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
              (FStar_List.rev names1))

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
          let uu____4995 = encode_term t env  in
          match uu____4995 with
          | (t1,decls) ->
              let uu____5006 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5006, decls)

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
          let uu____5017 = encode_term t env  in
          match uu____5017 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5032 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5032, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5034 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5034, decls))

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
        let uu____5040 = encode_args args_e env  in
        match uu____5040 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5059 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5069 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5069  in
            let binary arg_tms1 =
              let uu____5083 =
                let uu____5084 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5084  in
              let uu____5085 =
                let uu____5086 =
                  let uu____5087 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5087  in
                FStar_SMTEncoding_Term.unboxInt uu____5086  in
              (uu____5083, uu____5085)  in
            let mk_default uu____5094 =
              let uu____5095 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5095 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l a op mk_args ts =
              let uu____5149 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5149
              then
                let uu____5150 =
                  let uu____5151 = mk_args ts  in op uu____5151  in
                FStar_All.pipe_right uu____5150 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5183 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5183
              then
                let uu____5184 = binary ts  in
                match uu____5184 with
                | (t1,t2) ->
                    let uu____5191 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5191
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5195 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5195
                 then
                   let uu____5196 =
                     let uu____5197 = binary ts  in op uu____5197  in
                   FStar_All.pipe_right uu____5196
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 =
              mk_l ()
                (fun a246  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a246)
                (fun a247  -> (Obj.magic binary) a247)
               in
            let sub1 =
              mk_l ()
                (fun a248  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a248)
                (fun a249  -> (Obj.magic binary) a249)
               in
            let minus =
              mk_l ()
                (fun a250  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a250)
                (fun a251  -> (Obj.magic unary) a251)
               in
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
            let uu____5344 =
              let uu____5354 =
                FStar_List.tryFind
                  (fun uu____5378  ->
                     match uu____5378 with
                     | (l,uu____5388) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5354 FStar_Util.must  in
            (match uu____5344 with
             | (uu____5432,op) ->
                 let uu____5444 = op arg_tms  in (uu____5444, decls))

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
        let uu____5452 = FStar_List.hd args_e  in
        match uu____5452 with
        | (tm_sz,uu____5460) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5470 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5470 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  let uu____5477 =
                    let uu____5478 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5478  in
                  t_decls1
               in
            let uu____5479 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5499::(sz_arg,uu____5501)::uu____5502::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5551 =
                    let uu____5554 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5554  in
                  let uu____5557 =
                    let uu____5560 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5560  in
                  (uu____5551, uu____5557)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5566::(sz_arg,uu____5568)::uu____5569::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5618 =
                    let uu____5619 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5619
                     in
                  failwith uu____5618
              | uu____5628 ->
                  let uu____5635 = FStar_List.tail args_e  in
                  (uu____5635, FStar_Pervasives_Native.None)
               in
            (match uu____5479 with
             | (arg_tms,ext_sz) ->
                 let uu____5658 = encode_args arg_tms env  in
                 (match uu____5658 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5679 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5689 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5689  in
                      let unary_arith arg_tms2 =
                        let uu____5699 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5699  in
                      let binary arg_tms2 =
                        let uu____5713 =
                          let uu____5714 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5714
                           in
                        let uu____5715 =
                          let uu____5716 =
                            let uu____5717 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5717  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5716
                           in
                        (uu____5713, uu____5715)  in
                      let binary_arith arg_tms2 =
                        let uu____5733 =
                          let uu____5734 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5734
                           in
                        let uu____5735 =
                          let uu____5736 =
                            let uu____5737 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5737  in
                          FStar_SMTEncoding_Term.unboxInt uu____5736  in
                        (uu____5733, uu____5735)  in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5784 =
                          let uu____5785 = mk_args ts  in op uu____5785  in
                        FStar_All.pipe_right uu____5784 resBox  in
                      let bv_and =
                        mk_bv ()
                          (fun a252  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a252)
                          (fun a253  -> (Obj.magic binary) a253)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv ()
                          (fun a254  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a254)
                          (fun a255  -> (Obj.magic binary) a255)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv ()
                          (fun a256  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a256)
                          (fun a257  -> (Obj.magic binary) a257)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv ()
                          (fun a258  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a258)
                          (fun a259  -> (Obj.magic binary) a259)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv ()
                          (fun a260  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a260)
                          (fun a261  -> (Obj.magic binary) a261)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv ()
                          (fun a262  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a262)
                          (fun a263  -> (Obj.magic binary_arith) a263)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv ()
                          (fun a264  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a264)
                          (fun a265  -> (Obj.magic binary_arith) a265)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv ()
                          (fun a266  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a266)
                          (fun a267  -> (Obj.magic binary_arith) a267)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv ()
                          (fun a268  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a268)
                          (fun a269  -> (Obj.magic binary_arith) a269)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv ()
                          (fun a270  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a270)
                          (fun a271  -> (Obj.magic binary_arith) a271)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv ()
                          (fun a272  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a272)
                          (fun a273  -> (Obj.magic binary) a273)
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____5861 =
                          let uu____5865 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5865  in
                        let uu____5867 =
                          let uu____5871 =
                            let uu____5872 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5872  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5871  in
                        mk_bv () (fun a274  -> (Obj.magic uu____5861) a274)
                          (fun a275  -> (Obj.magic unary) a275) uu____5867
                          arg_tms2
                         in
                      let to_int1 =
                        mk_bv ()
                          (fun a276  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a276) (fun a277  -> (Obj.magic unary) a277)
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv ()
                          (fun a278  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a278)
                          (fun a279  -> (Obj.magic unary_arith) a279)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
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
                      let uu____6103 =
                        let uu____6113 =
                          FStar_List.tryFind
                            (fun uu____6137  ->
                               match uu____6137 with
                               | (l,uu____6147) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6113 FStar_Util.must  in
                      (match uu____6103 with
                       | (uu____6193,op) ->
                           let uu____6205 = op arg_tms1  in
                           (uu____6205, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      let uu____6215 =
        let uu____6216 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____6216
        then
          let uu____6217 = FStar_Syntax_Print.tag_of_term t  in
          let uu____6218 = FStar_Syntax_Print.tag_of_term t0  in
          let uu____6219 = FStar_Syntax_Print.term_to_string t0  in
          FStar_Util.print3 "(%s) (%s)   %s\n" uu____6217 uu____6218
            uu____6219
        else ()  in
      match t0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____6225 ->
          let uu____6250 =
            let uu____6251 =
              FStar_All.pipe_left FStar_Range.string_of_range
                t.FStar_Syntax_Syntax.pos
               in
            let uu____6252 = FStar_Syntax_Print.tag_of_term t0  in
            let uu____6253 = FStar_Syntax_Print.term_to_string t0  in
            let uu____6254 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6251
              uu____6252 uu____6253 uu____6254
             in
          failwith uu____6250
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6259 =
            let uu____6260 =
              FStar_All.pipe_left FStar_Range.string_of_range
                t.FStar_Syntax_Syntax.pos
               in
            let uu____6261 = FStar_Syntax_Print.tag_of_term t0  in
            let uu____6262 = FStar_Syntax_Print.term_to_string t0  in
            let uu____6263 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6260
              uu____6261 uu____6262 uu____6263
             in
          failwith uu____6259
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6269 = FStar_Syntax_Util.unfold_lazy i  in
          encode_term uu____6269 env
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6271 =
            let uu____6272 = FStar_Syntax_Print.bv_to_string x  in
            FStar_Util.format1 "Impossible: locally nameless; got %s"
              uu____6272
             in
          failwith uu____6271
      | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____6279),uu____6280) ->
          let uu____6329 =
            match k with
            | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
            | uu____6337 -> false  in
          if uu____6329
          then (FStar_SMTEncoding_Term.mk_Term_unit, [])
          else encode_term t1 env
      | FStar_Syntax_Syntax.Tm_quoted (qt,uu____6354) ->
          let tv =
            let uu____6360 = FStar_Reflection_Basic.inspect_ln qt  in
            FStar_Syntax_Embeddings.embed
              FStar_Reflection_Embeddings.e_term_view
              t.FStar_Syntax_Syntax.pos uu____6360
             in
          let t1 =
            let uu____6364 =
              let uu____6373 = FStar_Syntax_Syntax.as_arg tv  in [uu____6373]
               in
            FStar_Syntax_Util.mk_app
              (FStar_Reflection_Data.refl_constant_term
                 FStar_Reflection_Data.fstar_refl_pack_ln) uu____6364
             in
          encode_term t1 env
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____6375) -> encode_term t1 env
      | FStar_Syntax_Syntax.Tm_name x ->
          let t1 = lookup_term_var env x  in (t1, [])
      | FStar_Syntax_Syntax.Tm_fvar v1 ->
          let uu____6385 = lookup_free_var env v1.FStar_Syntax_Syntax.fv_name
             in
          (uu____6385, [])
      | FStar_Syntax_Syntax.Tm_type uu____6388 ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6392) -> encode_term t1 env
      | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
      | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
          let module_name = env.current_module_name  in
          let uu____6417 = FStar_Syntax_Subst.open_comp binders c  in
          (match uu____6417 with
           | (binders1,res) ->
               let uu____6428 =
                 (env.encode_non_total_function_typ &&
                    (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                   || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                  in
               if uu____6428
               then
                 let uu____6433 =
                   encode_binders FStar_Pervasives_Native.None binders1 env
                    in
                 (match uu____6433 with
                  | (vars,guards,env',decls,uu____6458) ->
                      let fsym =
                        let uu____6476 = varops.fresh "f"  in
                        (uu____6476, FStar_SMTEncoding_Term.Term_sort)  in
                      let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                      let app = mk_Apply f vars  in
                      let uu____6479 =
                        FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                          (let uu___113_6488 = env.tcenv  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___113_6488.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___113_6488.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___113_6488.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___113_6488.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___113_6488.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___113_6488.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___113_6488.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___113_6488.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___113_6488.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___113_6488.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___113_6488.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___113_6488.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___113_6488.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___113_6488.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___113_6488.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___113_6488.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___113_6488.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___113_6488.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___113_6488.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___113_6488.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___113_6488.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___113_6488.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___113_6488.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___113_6488.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___113_6488.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___113_6488.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___113_6488.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___113_6488.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___113_6488.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___113_6488.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___113_6488.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___113_6488.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___113_6488.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___113_6488.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___113_6488.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___113_6488.FStar_TypeChecker_Env.dep_graph)
                           }) res
                         in
                      (match uu____6479 with
                       | (pre_opt,res_t) ->
                           let uu____6499 =
                             encode_term_pred FStar_Pervasives_Native.None
                               res_t env' app
                              in
                           (match uu____6499 with
                            | (res_pred,decls') ->
                                let uu____6510 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____6523 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____6523, [])
                                  | FStar_Pervasives_Native.Some pre ->
                                      let uu____6527 =
                                        encode_formula pre env'  in
                                      (match uu____6527 with
                                       | (guard,decls0) ->
                                           let uu____6540 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (guard :: guards)
                                              in
                                           (uu____6540, decls0))
                                   in
                                (match uu____6510 with
                                 | (guards1,guard_decls) ->
                                     let t_interp =
                                       let uu____6552 =
                                         let uu____6563 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (guards1, res_pred)
                                            in
                                         ([[app]], vars, uu____6563)  in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____6552
                                        in
                                     let cvars =
                                       let uu____6581 =
                                         FStar_SMTEncoding_Term.free_variables
                                           t_interp
                                          in
                                       FStar_All.pipe_right uu____6581
                                         (FStar_List.filter
                                            (fun uu____6595  ->
                                               match uu____6595 with
                                               | (x,uu____6601) ->
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
                                     let uu____6620 =
                                       FStar_Util.smap_try_find env.cache
                                         tkey_hash
                                        in
                                     (match uu____6620 with
                                      | FStar_Pervasives_Native.Some
                                          cache_entry ->
                                          let uu____6628 =
                                            let uu____6629 =
                                              let uu____6636 =
                                                FStar_All.pipe_right cvars
                                                  (FStar_List.map
                                                     FStar_SMTEncoding_Util.mkFreeV)
                                                 in
                                              ((cache_entry.cache_symbol_name),
                                                uu____6636)
                                               in
                                            FStar_SMTEncoding_Util.mkApp
                                              uu____6629
                                             in
                                          (uu____6628,
                                            (FStar_List.append decls
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     (use_cache_entry
                                                        cache_entry)))))
                                      | FStar_Pervasives_Native.None  ->
                                          let tsym =
                                            let uu____6656 =
                                              let uu____6657 =
                                                FStar_Util.digest_of_string
                                                  tkey_hash
                                                 in
                                              Prims.strcat "Tm_arrow_"
                                                uu____6657
                                               in
                                            varops.mk_unique uu____6656  in
                                          let cvar_sorts =
                                            FStar_List.map
                                              FStar_Pervasives_Native.snd
                                              cvars
                                             in
                                          let caption =
                                            let uu____6668 =
                                              FStar_Options.log_queries ()
                                               in
                                            if uu____6668
                                            then
                                              let uu____6671 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env.tcenv t0
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____6671
                                            else FStar_Pervasives_Native.None
                                             in
                                          let tdecl =
                                            FStar_SMTEncoding_Term.DeclFun
                                              (tsym, cvar_sorts,
                                                FStar_SMTEncoding_Term.Term_sort,
                                                caption)
                                             in
                                          let t1 =
                                            let uu____6679 =
                                              let uu____6686 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (tsym, uu____6686)  in
                                            FStar_SMTEncoding_Util.mkApp
                                              uu____6679
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
                                            let uu____6698 =
                                              let uu____6705 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  ([[t_has_kind]], cvars,
                                                    t_has_kind)
                                                 in
                                              (uu____6705,
                                                (FStar_Pervasives_Native.Some
                                                   a_name), a_name)
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____6698
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
                                              Prims.strcat "pre_typing_" tsym
                                               in
                                            let uu____6726 =
                                              let uu____6733 =
                                                let uu____6734 =
                                                  let uu____6745 =
                                                    let uu____6746 =
                                                      let uu____6751 =
                                                        let uu____6752 =
                                                          FStar_SMTEncoding_Term.mk_PreType
                                                            f
                                                           in
                                                        FStar_SMTEncoding_Term.mk_tester
                                                          "Tm_arrow"
                                                          uu____6752
                                                         in
                                                      (f_has_t, uu____6751)
                                                       in
                                                    FStar_SMTEncoding_Util.mkImp
                                                      uu____6746
                                                     in
                                                  ([[f_has_t]], (fsym ::
                                                    cvars), uu____6745)
                                                   in
                                                mkForall_fuel uu____6734  in
                                              (uu____6733,
                                                (FStar_Pervasives_Native.Some
                                                   "pre-typing for functions"),
                                                (Prims.strcat module_name
                                                   (Prims.strcat "_" a_name)))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____6726
                                             in
                                          let t_interp1 =
                                            let a_name =
                                              Prims.strcat "interpretation_"
                                                tsym
                                               in
                                            let uu____6775 =
                                              let uu____6782 =
                                                let uu____6783 =
                                                  let uu____6794 =
                                                    FStar_SMTEncoding_Util.mkIff
                                                      (f_has_t_z, t_interp)
                                                     in
                                                  ([[f_has_t_z]], (fsym ::
                                                    cvars), uu____6794)
                                                   in
                                                FStar_SMTEncoding_Util.mkForall
                                                  uu____6783
                                                 in
                                              (uu____6782,
                                                (FStar_Pervasives_Native.Some
                                                   a_name),
                                                (Prims.strcat module_name
                                                   (Prims.strcat "_" a_name)))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____6775
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
                                          let uu____6818 =
                                            let uu____6819 =
                                              mk_cache_entry env tsym
                                                cvar_sorts t_decls1
                                               in
                                            FStar_Util.smap_add env.cache
                                              tkey_hash uu____6819
                                             in
                                          (t1, t_decls1))))))
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
                    let uu____6834 =
                      let uu____6841 =
                        FStar_SMTEncoding_Term.mk_HasType t1
                          FStar_SMTEncoding_Term.mk_Term_type
                         in
                      (uu____6841,
                        (FStar_Pervasives_Native.Some
                           "Typing for non-total arrows"),
                        (Prims.strcat module_name (Prims.strcat "_" a_name)))
                       in
                    FStar_SMTEncoding_Util.mkAssume uu____6834  in
                  let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                  let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                  let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                  let t_interp =
                    let a_name = Prims.strcat "pre_typing_" tsym  in
                    let uu____6853 =
                      let uu____6860 =
                        let uu____6861 =
                          let uu____6872 =
                            let uu____6873 =
                              let uu____6878 =
                                let uu____6879 =
                                  FStar_SMTEncoding_Term.mk_PreType f  in
                                FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                  uu____6879
                                 in
                              (f_has_t, uu____6878)  in
                            FStar_SMTEncoding_Util.mkImp uu____6873  in
                          ([[f_has_t]], [fsym], uu____6872)  in
                        mkForall_fuel uu____6861  in
                      (uu____6860, (FStar_Pervasives_Native.Some a_name),
                        (Prims.strcat module_name (Prims.strcat "_" a_name)))
                       in
                    FStar_SMTEncoding_Util.mkAssume uu____6853  in
                  (t1, [tdecl; t_kinding; t_interp])))
      | FStar_Syntax_Syntax.Tm_refine uu____6906 ->
          let uu____6913 =
            let uu____6918 =
              FStar_TypeChecker_Normalize.normalize_refinement
                [FStar_TypeChecker_Normalize.Weak;
                FStar_TypeChecker_Normalize.HNF;
                FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
               in
            match uu____6918 with
            | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                FStar_Syntax_Syntax.pos = uu____6925;
                FStar_Syntax_Syntax.vars = uu____6926;_} ->
                let uu____6933 =
                  FStar_Syntax_Subst.open_term
                    [(x, FStar_Pervasives_Native.None)] f
                   in
                (match uu____6933 with
                 | (b,f1) ->
                     let uu____6958 =
                       let uu____6959 = FStar_List.hd b  in
                       FStar_Pervasives_Native.fst uu____6959  in
                     (uu____6958, f1))
            | uu____6968 -> failwith "impossible"  in
          (match uu____6913 with
           | (x,f) ->
               let uu____6979 = encode_term x.FStar_Syntax_Syntax.sort env
                  in
               (match uu____6979 with
                | (base_t,decls) ->
                    let uu____6990 = gen_term_var env x  in
                    (match uu____6990 with
                     | (x1,xtm,env') ->
                         let uu____7004 = encode_formula f env'  in
                         (match uu____7004 with
                          | (refinement,decls') ->
                              let uu____7015 =
                                fresh_fvar "f"
                                  FStar_SMTEncoding_Term.Fuel_sort
                                 in
                              (match uu____7015 with
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
                                     let uu____7031 =
                                       let uu____7034 =
                                         FStar_SMTEncoding_Term.free_variables
                                           refinement
                                          in
                                       let uu____7041 =
                                         FStar_SMTEncoding_Term.free_variables
                                           tm_has_type_with_fuel
                                          in
                                       FStar_List.append uu____7034
                                         uu____7041
                                        in
                                     FStar_Util.remove_dups
                                       FStar_SMTEncoding_Term.fv_eq
                                       uu____7031
                                      in
                                   let cvars1 =
                                     FStar_All.pipe_right cvars
                                       (FStar_List.filter
                                          (fun uu____7074  ->
                                             match uu____7074 with
                                             | (y,uu____7080) ->
                                                 (y <> x1) && (y <> fsym)))
                                      in
                                   let xfv =
                                     (x1, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   let ffv =
                                     (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                                      in
                                   let tkey =
                                     FStar_SMTEncoding_Util.mkForall
                                       ([], (ffv :: xfv :: cvars1), encoding)
                                      in
                                   let tkey_hash =
                                     FStar_SMTEncoding_Term.hash_of_term tkey
                                      in
                                   let uu____7113 =
                                     FStar_Util.smap_try_find env.cache
                                       tkey_hash
                                      in
                                   (match uu____7113 with
                                    | FStar_Pervasives_Native.Some
                                        cache_entry ->
                                        let uu____7121 =
                                          let uu____7122 =
                                            let uu____7129 =
                                              FStar_All.pipe_right cvars1
                                                (FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV)
                                               in
                                            ((cache_entry.cache_symbol_name),
                                              uu____7129)
                                             in
                                          FStar_SMTEncoding_Util.mkApp
                                            uu____7122
                                           in
                                        (uu____7121,
                                          (FStar_List.append decls
                                             (FStar_List.append decls'
                                                (use_cache_entry cache_entry))))
                                    | FStar_Pervasives_Native.None  ->
                                        let module_name =
                                          env.current_module_name  in
                                        let tsym =
                                          let uu____7150 =
                                            let uu____7151 =
                                              let uu____7152 =
                                                FStar_Util.digest_of_string
                                                  tkey_hash
                                                 in
                                              Prims.strcat "_Tm_refine_"
                                                uu____7152
                                               in
                                            Prims.strcat module_name
                                              uu____7151
                                             in
                                          varops.mk_unique uu____7150  in
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
                                          let uu____7166 =
                                            let uu____7173 =
                                              FStar_List.map
                                                FStar_SMTEncoding_Util.mkFreeV
                                                cvars1
                                               in
                                            (tsym, uu____7173)  in
                                          FStar_SMTEncoding_Util.mkApp
                                            uu____7166
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
                                          let uu____7188 =
                                            let uu____7195 =
                                              let uu____7196 =
                                                let uu____7207 =
                                                  FStar_SMTEncoding_Util.mkIff
                                                    (t_haseq_ref,
                                                      t_haseq_base)
                                                   in
                                                ([[t_haseq_ref]], cvars1,
                                                  uu____7207)
                                                 in
                                              FStar_SMTEncoding_Util.mkForall
                                                uu____7196
                                               in
                                            (uu____7195,
                                              (FStar_Pervasives_Native.Some
                                                 (Prims.strcat "haseq for "
                                                    tsym)),
                                              (Prims.strcat "haseq" tsym))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____7188
                                           in
                                        let t_kinding =
                                          let uu____7225 =
                                            let uu____7232 =
                                              FStar_SMTEncoding_Util.mkForall
                                                ([[t_has_kind]], cvars1,
                                                  t_has_kind)
                                               in
                                            (uu____7232,
                                              (FStar_Pervasives_Native.Some
                                                 "refinement kinding"),
                                              (Prims.strcat
                                                 "refinement_kinding_" tsym))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____7225
                                           in
                                        let t_interp =
                                          let uu____7250 =
                                            let uu____7257 =
                                              let uu____7258 =
                                                let uu____7269 =
                                                  FStar_SMTEncoding_Util.mkIff
                                                    (x_has_t, encoding)
                                                   in
                                                ([[x_has_t]], (ffv :: xfv ::
                                                  cvars1), uu____7269)
                                                 in
                                              FStar_SMTEncoding_Util.mkForall
                                                uu____7258
                                               in
                                            let uu____7292 =
                                              let uu____7295 =
                                                FStar_Syntax_Print.term_to_string
                                                  t0
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____7295
                                               in
                                            (uu____7257, uu____7292,
                                              (Prims.strcat
                                                 "refinement_interpretation_"
                                                 tsym))
                                             in
                                          FStar_SMTEncoding_Util.mkAssume
                                            uu____7250
                                           in
                                        let t_decls1 =
                                          FStar_List.append decls
                                            (FStar_List.append decls'
                                               [tdecl;
                                               t_kinding;
                                               t_interp;
                                               t_haseq1])
                                           in
                                        let uu____7301 =
                                          let uu____7302 =
                                            mk_cache_entry env tsym
                                              cvar_sorts t_decls1
                                             in
                                          FStar_Util.smap_add env.cache
                                            tkey_hash uu____7302
                                           in
                                        (t1, t_decls1)))))))
      | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
          let ttm =
            let uu____7332 = FStar_Syntax_Unionfind.uvar_id uv  in
            FStar_SMTEncoding_Util.mk_Term_uvar uu____7332  in
          let uu____7333 =
            encode_term_pred FStar_Pervasives_Native.None k env ttm  in
          (match uu____7333 with
           | (t_has_k,decls) ->
               let d =
                 let uu____7345 =
                   let uu____7352 =
                     let uu____7353 =
                       let uu____7354 =
                         let uu____7355 = FStar_Syntax_Unionfind.uvar_id uv
                            in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7355
                          in
                       FStar_Util.format1 "uvar_typing_%s" uu____7354  in
                     varops.mk_unique uu____7353  in
                   (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                     uu____7352)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____7345  in
               (ttm, (FStar_List.append decls [d])))
      | FStar_Syntax_Syntax.Tm_app uu____7360 ->
          let uu____7375 = FStar_Syntax_Util.head_and_args t0  in
          (match uu____7375 with
           | (head1,args_e) ->
               let uu____7416 =
                 let uu____7429 =
                   let uu____7430 = FStar_Syntax_Subst.compress head1  in
                   uu____7430.FStar_Syntax_Syntax.n  in
                 (uu____7429, args_e)  in
               (match uu____7416 with
                | uu____7445 when head_redex env head1 ->
                    let uu____7458 = whnf env t  in
                    encode_term uu____7458 env
                | uu____7459 when is_arithmetic_primitive head1 args_e ->
                    encode_arith_term env head1 args_e
                | uu____7478 when is_BitVector_primitive head1 args_e ->
                    encode_BitVector_term env head1 args_e
                | (FStar_Syntax_Syntax.Tm_uinst
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____7492;
                      FStar_Syntax_Syntax.vars = uu____7493;_},uu____7494),uu____7495::
                   (v1,uu____7497)::(v2,uu____7499)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.lexcons_lid
                    ->
                    let uu____7550 = encode_term v1 env  in
                    (match uu____7550 with
                     | (v11,decls1) ->
                         let uu____7561 = encode_term v2 env  in
                         (match uu____7561 with
                          | (v21,decls2) ->
                              let uu____7572 =
                                FStar_SMTEncoding_Util.mk_LexCons v11 v21  in
                              (uu____7572, (FStar_List.append decls1 decls2))))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____7576::(v1,uu____7578)::(v2,uu____7580)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.lexcons_lid
                    ->
                    let uu____7627 = encode_term v1 env  in
                    (match uu____7627 with
                     | (v11,decls1) ->
                         let uu____7638 = encode_term v2 env  in
                         (match uu____7638 with
                          | (v21,decls2) ->
                              let uu____7649 =
                                FStar_SMTEncoding_Util.mk_LexCons v11 v21  in
                              (uu____7649, (FStar_List.append decls1 decls2))))
                | (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_range_of ),(arg,uu____7653)::[]) ->
                    encode_const
                      (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                      env
                | (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_set_range_of
                   ),(arg,uu____7679)::(rng,uu____7681)::[]) ->
                    encode_term arg env
                | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                   ),uu____7716) ->
                    let e0 =
                      let uu____7734 = FStar_List.hd args_e  in
                      FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                        head1 uu____7734
                       in
                    let uu____7741 =
                      let uu____7742 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env.tcenv)
                          (FStar_Options.Other "SMTEncodingReify")
                         in
                      if uu____7742
                      then
                        let uu____7743 = FStar_Syntax_Print.term_to_string e0
                           in
                        FStar_Util.print1 "Result of normalization %s\n"
                          uu____7743
                      else ()  in
                    let e =
                      let uu____7748 =
                        let uu____7751 =
                          FStar_TypeChecker_Util.remove_reify e0  in
                        let uu____7752 = FStar_List.tl args_e  in
                        FStar_Syntax_Syntax.mk_Tm_app uu____7751 uu____7752
                         in
                      uu____7748 FStar_Pervasives_Native.None
                        t0.FStar_Syntax_Syntax.pos
                       in
                    encode_term e env
                | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
                   uu____7761),(arg,uu____7763)::[]) -> encode_term arg env
                | uu____7788 ->
                    let uu____7801 = encode_args args_e env  in
                    (match uu____7801 with
                     | (args,decls) ->
                         let encode_partial_app ht_opt =
                           let uu____7857 = encode_term head1 env  in
                           match uu____7857 with
                           | (head2,decls') ->
                               let app_tm = mk_Apply_args head2 args  in
                               (match ht_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (app_tm,
                                      (FStar_List.append decls decls'))
                                | FStar_Pervasives_Native.Some (formals,c) ->
                                    let uu____7921 =
                                      FStar_Util.first_N
                                        (FStar_List.length args_e) formals
                                       in
                                    (match uu____7921 with
                                     | (formals1,rest) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun uu____7999  ->
                                                fun uu____8000  ->
                                                  match (uu____7999,
                                                          uu____8000)
                                                  with
                                                  | ((bv,uu____8022),
                                                     (a,uu____8024)) ->
                                                      FStar_Syntax_Syntax.NT
                                                        (bv, a)) formals1
                                             args_e
                                            in
                                         let ty =
                                           let uu____8042 =
                                             FStar_Syntax_Util.arrow rest c
                                              in
                                           FStar_All.pipe_right uu____8042
                                             (FStar_Syntax_Subst.subst subst1)
                                            in
                                         let uu____8047 =
                                           encode_term_pred
                                             FStar_Pervasives_Native.None ty
                                             env app_tm
                                            in
                                         (match uu____8047 with
                                          | (has_type,decls'') ->
                                              let cvars =
                                                FStar_SMTEncoding_Term.free_variables
                                                  has_type
                                                 in
                                              let e_typing =
                                                let uu____8062 =
                                                  let uu____8069 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      ([[has_type]], cvars,
                                                        has_type)
                                                     in
                                                  let uu____8078 =
                                                    let uu____8079 =
                                                      let uu____8080 =
                                                        let uu____8081 =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm
                                                           in
                                                        FStar_Util.digest_of_string
                                                          uu____8081
                                                         in
                                                      Prims.strcat
                                                        "partial_app_typing_"
                                                        uu____8080
                                                       in
                                                    varops.mk_unique
                                                      uu____8079
                                                     in
                                                  (uu____8069,
                                                    (FStar_Pervasives_Native.Some
                                                       "Partial app typing"),
                                                    uu____8078)
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____8062
                                                 in
                                              (app_tm,
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      (FStar_List.append
                                                         decls'' [e_typing])))))))
                            in
                         let encode_full_app fv =
                           let uu____8099 = lookup_free_var_sym env fv  in
                           match uu____8099 with
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
                                  FStar_Syntax_Syntax.pos = uu____8131;
                                  FStar_Syntax_Syntax.vars = uu____8132;_},uu____8133)
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
                                  FStar_Syntax_Syntax.pos = uu____8144;
                                  FStar_Syntax_Syntax.vars = uu____8145;_},uu____8146)
                               ->
                               let uu____8151 =
                                 let uu____8152 =
                                   let uu____8157 =
                                     FStar_TypeChecker_Env.lookup_lid
                                       env.tcenv
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   FStar_All.pipe_right uu____8157
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_All.pipe_right uu____8152
                                   FStar_Pervasives_Native.snd
                                  in
                               FStar_Pervasives_Native.Some uu____8151
                           | FStar_Syntax_Syntax.Tm_fvar fv ->
                               let uu____8187 =
                                 let uu____8188 =
                                   let uu____8193 =
                                     FStar_TypeChecker_Env.lookup_lid
                                       env.tcenv
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   FStar_All.pipe_right uu____8193
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_All.pipe_right uu____8188
                                   FStar_Pervasives_Native.snd
                                  in
                               FStar_Pervasives_Native.Some uu____8187
                           | FStar_Syntax_Syntax.Tm_ascribed
                               (uu____8222,(FStar_Util.Inl t1,uu____8224),uu____8225)
                               -> FStar_Pervasives_Native.Some t1
                           | FStar_Syntax_Syntax.Tm_ascribed
                               (uu____8274,(FStar_Util.Inr c,uu____8276),uu____8277)
                               ->
                               FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.comp_result c)
                           | uu____8326 -> FStar_Pervasives_Native.None  in
                         (match head_type with
                          | FStar_Pervasives_Native.None  ->
                              encode_partial_app FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some head_type1 ->
                              let head_type2 =
                                let uu____8353 =
                                  FStar_TypeChecker_Normalize.normalize_refinement
                                    [FStar_TypeChecker_Normalize.Weak;
                                    FStar_TypeChecker_Normalize.HNF;
                                    FStar_TypeChecker_Normalize.EraseUniverses]
                                    env.tcenv head_type1
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.unrefine uu____8353
                                 in
                              let uu____8354 =
                                curried_arrow_formals_comp head_type2  in
                              (match uu____8354 with
                               | (formals,c) ->
                                   (match head2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_uinst
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____8370;
                                           FStar_Syntax_Syntax.vars =
                                             uu____8371;_},uu____8372)
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
                                    | uu____8386 ->
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
          let uu____8435 = FStar_Syntax_Subst.open_term' bs body  in
          (match uu____8435 with
           | (bs1,body1,opening) ->
               let fallback uu____8459 =
                 let f = varops.fresh "Tm_abs"  in
                 let decl =
                   FStar_SMTEncoding_Term.DeclFun
                     (f, [], FStar_SMTEncoding_Term.Term_sort,
                       (FStar_Pervasives_Native.Some
                          "Imprecise function encoding"))
                    in
                 let uu____8466 =
                   FStar_SMTEncoding_Util.mkFreeV
                     (f, FStar_SMTEncoding_Term.Term_sort)
                    in
                 (uu____8466, [decl])  in
               let is_impure rc =
                 let uu____8474 =
                   FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                     rc.FStar_Syntax_Syntax.residual_effect
                    in
                 FStar_All.pipe_right uu____8474 Prims.op_Negation  in
               let codomain_eff rc =
                 let res_typ =
                   match rc.FStar_Syntax_Syntax.residual_typ with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8485 =
                         FStar_TypeChecker_Rel.new_uvar
                           FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_right uu____8485
                         FStar_Pervasives_Native.fst
                   | FStar_Pervasives_Native.Some t1 -> t1  in
                 let uu____8503 =
                   FStar_Ident.lid_equals
                     rc.FStar_Syntax_Syntax.residual_effect
                     FStar_Parser_Const.effect_Tot_lid
                    in
                 if uu____8503
                 then
                   let uu____8506 = FStar_Syntax_Syntax.mk_Total res_typ  in
                   FStar_Pervasives_Native.Some uu____8506
                 else
                   (let uu____8508 =
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                       in
                    if uu____8508
                    then
                      let uu____8511 = FStar_Syntax_Syntax.mk_GTotal res_typ
                         in
                      FStar_Pervasives_Native.Some uu____8511
                    else FStar_Pervasives_Native.None)
                  in
               (match lopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____8517 =
                      let uu____8518 =
                        let uu____8523 =
                          let uu____8524 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1
                            "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                            uu____8524
                           in
                        (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                          uu____8523)
                         in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____8518
                       in
                    fallback ()
                | FStar_Pervasives_Native.Some rc ->
                    let uu____8526 =
                      (is_impure rc) &&
                        (let uu____8528 =
                           FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                            in
                         Prims.op_Negation uu____8528)
                       in
                    if uu____8526
                    then fallback ()
                    else
                      (let cache_size = FStar_Util.smap_size env.cache  in
                       let uu____8535 =
                         encode_binders FStar_Pervasives_Native.None bs1 env
                          in
                       match uu____8535 with
                       | (vars,guards,envbody,decls,uu____8560) ->
                           let body2 =
                             let uu____8574 =
                               FStar_TypeChecker_Env.is_reifiable env.tcenv
                                 rc
                                in
                             if uu____8574
                             then
                               FStar_TypeChecker_Util.reify_body env.tcenv
                                 body1
                             else body1  in
                           let uu____8576 = encode_term body2 envbody  in
                           (match uu____8576 with
                            | (body3,decls') ->
                                let uu____8587 =
                                  let uu____8596 = codomain_eff rc  in
                                  match uu____8596 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None, [])
                                  | FStar_Pervasives_Native.Some c ->
                                      let tfun =
                                        FStar_Syntax_Util.arrow bs1 c  in
                                      let uu____8615 = encode_term tfun env
                                         in
                                      (match uu____8615 with
                                       | (t1,decls1) ->
                                           ((FStar_Pervasives_Native.Some t1),
                                             decls1))
                                   in
                                (match uu____8587 with
                                 | (arrow_t_opt,decls'') ->
                                     let key_body =
                                       let uu____8647 =
                                         let uu____8658 =
                                           let uu____8659 =
                                             let uu____8664 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards
                                                in
                                             (uu____8664, body3)  in
                                           FStar_SMTEncoding_Util.mkImp
                                             uu____8659
                                            in
                                         ([], vars, uu____8658)  in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____8647
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
                                           let uu____8676 =
                                             let uu____8679 =
                                               FStar_SMTEncoding_Term.free_variables
                                                 t1
                                                in
                                             FStar_List.append uu____8679
                                               cvars
                                              in
                                           FStar_Util.remove_dups
                                             FStar_SMTEncoding_Term.fv_eq
                                             uu____8676
                                        in
                                     let tkey =
                                       FStar_SMTEncoding_Util.mkForall
                                         ([], cvars1, key_body)
                                        in
                                     let tkey_hash =
                                       FStar_SMTEncoding_Term.hash_of_term
                                         tkey
                                        in
                                     let uu____8698 =
                                       FStar_Util.smap_try_find env.cache
                                         tkey_hash
                                        in
                                     (match uu____8698 with
                                      | FStar_Pervasives_Native.Some
                                          cache_entry ->
                                          let uu____8706 =
                                            let uu____8707 =
                                              let uu____8714 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars1
                                                 in
                                              ((cache_entry.cache_symbol_name),
                                                uu____8714)
                                               in
                                            FStar_SMTEncoding_Util.mkApp
                                              uu____8707
                                             in
                                          (uu____8706,
                                            (FStar_List.append decls
                                               (FStar_List.append decls'
                                                  (FStar_List.append decls''
                                                     (use_cache_entry
                                                        cache_entry)))))
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8725 =
                                            is_an_eta_expansion env vars
                                              body3
                                             in
                                          (match uu____8725 with
                                           | FStar_Pervasives_Native.Some t1
                                               ->
                                               let decls1 =
                                                 let uu____8736 =
                                                   let uu____8737 =
                                                     FStar_Util.smap_size
                                                       env.cache
                                                      in
                                                   uu____8737 = cache_size
                                                    in
                                                 if uu____8736
                                                 then []
                                                 else
                                                   FStar_List.append decls
                                                     (FStar_List.append
                                                        decls' decls'')
                                                  in
                                               (t1, decls1)
                                           | FStar_Pervasives_Native.None  ->
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
                                                   let uu____8753 =
                                                     let uu____8754 =
                                                       FStar_Util.digest_of_string
                                                         tkey_hash
                                                        in
                                                     Prims.strcat "Tm_abs_"
                                                       uu____8754
                                                      in
                                                   varops.mk_unique
                                                     uu____8753
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
                                                 let uu____8761 =
                                                   let uu____8768 =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       cvars1
                                                      in
                                                   (fsym, uu____8768)  in
                                                 FStar_SMTEncoding_Util.mkApp
                                                   uu____8761
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
                                                       Prims.strcat "typing_"
                                                         fsym
                                                        in
                                                     let uu____8786 =
                                                       let uu____8787 =
                                                         let uu____8794 =
                                                           FStar_SMTEncoding_Util.mkForall
                                                             ([[f]], cvars1,
                                                               f_has_t)
                                                            in
                                                         (uu____8794,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____8787
                                                        in
                                                     [uu____8786]
                                                  in
                                               let interp_f =
                                                 let a_name =
                                                   Prims.strcat
                                                     "interpretation_" fsym
                                                    in
                                                 let uu____8807 =
                                                   let uu____8814 =
                                                     let uu____8815 =
                                                       let uu____8826 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (app, body3)
                                                          in
                                                       ([[app]],
                                                         (FStar_List.append
                                                            vars cvars1),
                                                         uu____8826)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____8815
                                                      in
                                                   (uu____8814,
                                                     (FStar_Pervasives_Native.Some
                                                        a_name), a_name)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8807
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
                                               let uu____8842 =
                                                 let uu____8843 =
                                                   mk_cache_entry env fsym
                                                     cvar_sorts f_decls
                                                    in
                                                 FStar_Util.smap_add
                                                   env.cache tkey_hash
                                                   uu____8843
                                                  in
                                               (f, f_decls))))))))
      | FStar_Syntax_Syntax.Tm_let
          ((uu____8846,{
                         FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                           uu____8847;
                         FStar_Syntax_Syntax.lbunivs = uu____8848;
                         FStar_Syntax_Syntax.lbtyp = uu____8849;
                         FStar_Syntax_Syntax.lbeff = uu____8850;
                         FStar_Syntax_Syntax.lbdef = uu____8851;
                         FStar_Syntax_Syntax.lbattrs = uu____8852;
                         FStar_Syntax_Syntax.lbpos = uu____8853;_}::uu____8854),uu____8855)
          -> failwith "Impossible: already handled by encoding of Sig_let"
      | FStar_Syntax_Syntax.Tm_let
          ((false
            ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu____8885;
               FStar_Syntax_Syntax.lbtyp = t1;
               FStar_Syntax_Syntax.lbeff = uu____8887;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu____8889;
               FStar_Syntax_Syntax.lbpos = uu____8890;_}::[]),e2)
          -> encode_let x t1 e1 e2 env encode_term
      | FStar_Syntax_Syntax.Tm_let uu____8914 ->
          let uu____8927 =
            FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts"
             in
          FStar_Exn.raise Inner_let_rec
      | FStar_Syntax_Syntax.Tm_match (e,pats) ->
          encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
            encode_term

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
              let uu____8984 =
                let uu____8989 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8989 env  in
              match uu____8984 with
              | (ee1,decls1) ->
                  let uu____9010 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9010 with
                   | (xs,e21) ->
                       let uu____9035 = FStar_List.hd xs  in
                       (match uu____9035 with
                        | (x1,uu____9049) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9051 = encode_body e21 env'  in
                            (match uu____9051 with
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
            let uu____9083 =
              let uu____9090 =
                let uu____9091 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9091  in
              gen_term_var env uu____9090  in
            match uu____9083 with
            | (scrsym,scr',env1) ->
                let uu____9099 = encode_term e env1  in
                (match uu____9099 with
                 | (scr,decls) ->
                     let uu____9110 =
                       let encode_branch b uu____9137 =
                         match uu____9137 with
                         | (else_case,decls1) ->
                             let uu____9156 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9156 with
                              | (p,w,br) ->
                                  let uu____9182 = encode_pat env1 p  in
                                  (match uu____9182 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9219  ->
                                                   match uu____9219 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9226 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9248 =
                                               encode_term w1 env2  in
                                             (match uu____9248 with
                                              | (w2,decls2) ->
                                                  let uu____9261 =
                                                    let uu____9262 =
                                                      let uu____9267 =
                                                        let uu____9268 =
                                                          let uu____9273 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9273)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9268
                                                         in
                                                      (guard, uu____9267)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9262
                                                     in
                                                  (uu____9261, decls2))
                                          in
                                       (match uu____9226 with
                                        | (guard1,decls2) ->
                                            let uu____9286 =
                                              encode_br br env2  in
                                            (match uu____9286 with
                                             | (br1,decls3) ->
                                                 let uu____9299 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9299,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9110 with
                      | (match_tm,decls1) ->
                          let uu____9318 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9318, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      let uu____9357 =
        let uu____9358 =
          FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
        if uu____9358
        then
          let uu____9359 = FStar_Syntax_Print.pat_to_string pat  in
          FStar_Util.print1 "Encoding pattern %s\n" uu____9359
        else ()  in
      let uu____9361 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
         in
      match uu____9361 with
      | (vars,pat_term) ->
          let uu____9378 =
            FStar_All.pipe_right vars
              (FStar_List.fold_left
                 (fun uu____9431  ->
                    fun v1  ->
                      match uu____9431 with
                      | (env1,vars1) ->
                          let uu____9483 = gen_term_var env1 v1  in
                          (match uu____9483 with
                           | (xx,uu____9505,env2) ->
                               (env2,
                                 ((v1,
                                    (xx, FStar_SMTEncoding_Term.Term_sort))
                                 :: vars1)))) (env, []))
             in
          (match uu____9378 with
           | (env1,vars1) ->
               let rec mk_guard pat1 scrutinee =
                 match pat1.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_var uu____9586 ->
                     FStar_SMTEncoding_Util.mkTrue
                 | FStar_Syntax_Syntax.Pat_wild uu____9587 ->
                     FStar_SMTEncoding_Util.mkTrue
                 | FStar_Syntax_Syntax.Pat_dot_term uu____9588 ->
                     FStar_SMTEncoding_Util.mkTrue
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____9596 = encode_const c env1  in
                     (match uu____9596 with
                      | (tm,decls) ->
                          let uu____9609 =
                            match decls with
                            | uu____9610::uu____9611 ->
                                failwith
                                  "Unexpected encoding of constant pattern"
                            | uu____9614 -> ()  in
                          FStar_SMTEncoding_Util.mkEq (scrutinee, tm))
                 | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                     let is_f =
                       let tc_name =
                         FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       let uu____9637 =
                         FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                           tc_name
                          in
                       match uu____9637 with
                       | (uu____9644,uu____9645::[]) ->
                           FStar_SMTEncoding_Util.mkTrue
                       | uu____9648 ->
                           mk_data_tester env1
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             scrutinee
                        in
                     let sub_term_guards =
                       FStar_All.pipe_right args
                         (FStar_List.mapi
                            (fun i  ->
                               fun uu____9681  ->
                                 match uu____9681 with
                                 | (arg,uu____9689) ->
                                     let proj =
                                       primitive_projector_by_pos env1.tcenv
                                         (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         i
                                        in
                                     let uu____9695 =
                                       FStar_SMTEncoding_Util.mkApp
                                         (proj, [scrutinee])
                                        in
                                     mk_guard arg uu____9695))
                        in
                     FStar_SMTEncoding_Util.mk_and_l (is_f ::
                       sub_term_guards)
                  in
               let rec mk_projections pat1 scrutinee =
                 match pat1.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9724) ->
                     [(x, scrutinee)]
                 | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                 | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                 | FStar_Syntax_Syntax.Pat_constant uu____9755 -> []
                 | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                     let uu____9778 =
                       FStar_All.pipe_right args
                         (FStar_List.mapi
                            (fun i  ->
                               fun uu____9822  ->
                                 match uu____9822 with
                                 | (arg,uu____9836) ->
                                     let proj =
                                       primitive_projector_by_pos env1.tcenv
                                         (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         i
                                        in
                                     let uu____9842 =
                                       FStar_SMTEncoding_Util.mkApp
                                         (proj, [scrutinee])
                                        in
                                     mk_projections arg uu____9842))
                        in
                     FStar_All.pipe_right uu____9778 FStar_List.flatten
                  in
               let pat_term1 uu____9871 = encode_term pat_term env1  in
               let pattern =
                 {
                   pat_vars = vars1;
                   pat_term = pat_term1;
                   guard = (mk_guard pat);
                   projections = (mk_projections pat)
                 }  in
               (env1, pattern))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____9881 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9919  ->
                fun uu____9920  ->
                  match (uu____9919, uu____9920) with
                  | ((tms,decls),(t,uu____9956)) ->
                      let uu____9977 = encode_term t env  in
                      (match uu____9977 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9881 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10035 = FStar_Syntax_Util.list_elements e  in
        match uu____10035 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            let uu____10049 =
              FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_NonListLiteralSMTPattern,
                  "SMT pattern is not a list literal; ignoring the pattern")
               in
            []
         in
      let one_pat p =
        let uu____10057 =
          let uu____10072 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10072 FStar_Syntax_Util.head_and_args
           in
        match uu____10057 with
        | (head1,args) ->
            let uu____10111 =
              let uu____10124 =
                let uu____10125 = FStar_Syntax_Util.un_uinst head1  in
                uu____10125.FStar_Syntax_Syntax.n  in
              (uu____10124, args)  in
            (match uu____10111 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10139,uu____10140)::(e,uu____10142)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10177 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____10215 =
            let uu____10230 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10230 FStar_Syntax_Util.head_and_args
             in
          match uu____10215 with
          | (head1,args) ->
              let uu____10271 =
                let uu____10284 =
                  let uu____10285 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10285.FStar_Syntax_Syntax.n  in
                (uu____10284, args)  in
              (match uu____10271 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10302)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10329 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10351 = smt_pat_or t1  in
            (match uu____10351 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10367 = list_elements1 e  in
                 FStar_All.pipe_right uu____10367
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10385 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10385
                           (FStar_List.map one_pat)))
             | uu____10396 ->
                 let uu____10401 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10401])
        | uu____10422 ->
            let uu____10425 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10425]
         in
      let uu____10446 =
        let uu____10465 =
          let uu____10466 = FStar_Syntax_Subst.compress t  in
          uu____10466.FStar_Syntax_Syntax.n  in
        match uu____10465 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10505 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10505 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10548;
                        FStar_Syntax_Syntax.effect_name = uu____10549;
                        FStar_Syntax_Syntax.result_typ = uu____10550;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10552)::(post,uu____10554)::(pats,uu____10556)::[];
                        FStar_Syntax_Syntax.flags = uu____10557;_}
                      ->
                      let uu____10598 = lemma_pats pats  in
                      (binders1, pre, post, uu____10598)
                  | uu____10615 -> failwith "impos"))
        | uu____10634 -> failwith "Impos"  in
      match uu____10446 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___114_10682 = env  in
            {
              bindings = (uu___114_10682.bindings);
              depth = (uu___114_10682.depth);
              tcenv = (uu___114_10682.tcenv);
              warn = (uu___114_10682.warn);
              cache = (uu___114_10682.cache);
              nolabels = (uu___114_10682.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___114_10682.encode_non_total_function_typ);
              current_module_name = (uu___114_10682.current_module_name)
            }  in
          let uu____10683 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10683 with
           | (vars,guards,env2,decls,uu____10708) ->
               let uu____10721 =
                 let uu____10736 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10790 =
                             let uu____10801 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10801
                               FStar_List.unzip
                              in
                           match uu____10790 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10736 FStar_List.unzip  in
               (match uu____10721 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___115_10953 = env2  in
                      {
                        bindings = (uu___115_10953.bindings);
                        depth = (uu___115_10953.depth);
                        tcenv = (uu___115_10953.tcenv);
                        warn = (uu___115_10953.warn);
                        cache = (uu___115_10953.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___115_10953.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___115_10953.encode_non_total_function_typ);
                        current_module_name =
                          (uu___115_10953.current_module_name)
                      }  in
                    let uu____10954 =
                      let uu____10959 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10959 env3  in
                    (match uu____10954 with
                     | (pre1,decls'') ->
                         let uu____10966 =
                           let uu____10971 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10971 env3  in
                         (match uu____10966 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10981 =
                                let uu____10982 =
                                  let uu____10993 =
                                    let uu____10994 =
                                      let uu____10999 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10999, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10994
                                     in
                                  (pats, vars, uu____10993)  in
                                FStar_SMTEncoding_Util.mkForall uu____10982
                                 in
                              (uu____10981, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____11012 = FStar_Syntax_Util.head_and_args t  in
      match uu____11012 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____11071::(x,uu____11073)::(t1,uu____11075)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____11122 = encode_term x env  in
               (match uu____11122 with
                | (x1,decls) ->
                    let uu____11135 = encode_term t1 env  in
                    (match uu____11135 with
                     | (t2,decls') ->
                         let uu____11148 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____11148, (FStar_List.append decls decls'))))
           | uu____11151 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11175 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____11175
        then
          let uu____11176 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____11177 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11176 uu____11177
        else ()  in
      let enc f r l =
        let uu____11215 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11243 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11243 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____11215 with
        | (decls,args) ->
            let uu____11272 =
              let uu___116_11273 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___116_11273.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___116_11273.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11272, decls)
         in
      let const_op f r uu____11307 =
        let uu____11320 = f r  in (uu____11320, [])  in
      let un_op f l =
        let uu____11341 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11341  in
      let bin_op f uu___90_11359 =
        match uu___90_11359 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11370 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11409 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11432  ->
                 match uu____11432 with
                 | (t,uu____11446) ->
                     let uu____11447 = encode_formula t env  in
                     (match uu____11447 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11409 with
        | (decls,phis) ->
            let uu____11476 =
              let uu___117_11477 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_11477.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_11477.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11476, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11540  ->
               match uu____11540 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11559) -> false
                    | uu____11560 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11575 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11575
        else
          (let uu____11589 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11589 r rf)
         in
      let mk_imp1 r uu___91_11620 =
        match uu___91_11620 with
        | (lhs,uu____11626)::(rhs,uu____11628)::[] ->
            let uu____11655 = encode_formula rhs env  in
            (match uu____11655 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11670) ->
                      (l1, decls1)
                  | uu____11675 ->
                      let uu____11676 = encode_formula lhs env  in
                      (match uu____11676 with
                       | (l2,decls2) ->
                           let uu____11687 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11687, (FStar_List.append decls1 decls2)))))
        | uu____11690 -> failwith "impossible"  in
      let mk_ite r uu___92_11715 =
        match uu___92_11715 with
        | (guard,uu____11721)::(_then,uu____11723)::(_else,uu____11725)::[]
            ->
            let uu____11762 = encode_formula guard env  in
            (match uu____11762 with
             | (g,decls1) ->
                 let uu____11773 = encode_formula _then env  in
                 (match uu____11773 with
                  | (t,decls2) ->
                      let uu____11784 = encode_formula _else env  in
                      (match uu____11784 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11798 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11825 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11825  in
      let connectives =
        let uu____11845 =
          let uu____11860 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11860)  in
        let uu____11881 =
          let uu____11898 =
            let uu____11913 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11913)  in
          let uu____11934 =
            let uu____11951 =
              let uu____11969 =
                let uu____11984 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11984)  in
              let uu____12005 =
                let uu____12022 =
                  let uu____12040 =
                    let uu____12055 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12055)  in
                  [uu____12040;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12022  in
              uu____11969 :: uu____12005  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11951  in
          uu____11898 :: uu____11934  in
        uu____11845 :: uu____11881  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12419 = encode_formula phi' env  in
            (match uu____12419 with
             | (phi2,decls) ->
                 let uu____12430 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12430, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12431 ->
            let uu____12438 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12438 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12477 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12477 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12489;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12491;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12493;
                 FStar_Syntax_Syntax.lbpos = uu____12494;_}::[]),e2)
            ->
            let uu____12518 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12518 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12565::(x,uu____12567)::(t,uu____12569)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12616 = encode_term x env  in
                 (match uu____12616 with
                  | (x1,decls) ->
                      let uu____12627 = encode_term t env  in
                      (match uu____12627 with
                       | (t1,decls') ->
                           let uu____12638 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12638, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12643)::(msg,uu____12645)::(phi2,uu____12647)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12692 =
                   let uu____12697 =
                     let uu____12698 = FStar_Syntax_Subst.compress r  in
                     uu____12698.FStar_Syntax_Syntax.n  in
                   let uu____12701 =
                     let uu____12702 = FStar_Syntax_Subst.compress msg  in
                     uu____12702.FStar_Syntax_Syntax.n  in
                   (uu____12697, uu____12701)  in
                 (match uu____12692 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12711))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12717 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12724)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12749 when head_redex env head2 ->
                 let uu____12762 = whnf env phi1  in
                 encode_formula uu____12762 env
             | uu____12763 ->
                 let uu____12776 = encode_term phi1 env  in
                 (match uu____12776 with
                  | (tt,decls) ->
                      let uu____12787 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___118_12790 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___118_12790.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___118_12790.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12787, decls)))
        | uu____12791 ->
            let uu____12792 = encode_term phi1 env  in
            (match uu____12792 with
             | (tt,decls) ->
                 let uu____12803 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___119_12806 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___119_12806.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___119_12806.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12803, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12846 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12846 with
        | (vars,guards,env2,decls,uu____12885) ->
            let uu____12898 =
              let uu____12911 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12963 =
                          let uu____12974 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____13014  ->
                                    match uu____13014 with
                                    | (t,uu____13028) ->
                                        encode_smt_pattern t
                                          (let uu___120_13034 = env2  in
                                           {
                                             bindings =
                                               (uu___120_13034.bindings);
                                             depth = (uu___120_13034.depth);
                                             tcenv = (uu___120_13034.tcenv);
                                             warn = (uu___120_13034.warn);
                                             cache = (uu___120_13034.cache);
                                             nolabels =
                                               (uu___120_13034.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___120_13034.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___120_13034.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12974 FStar_List.unzip
                           in
                        match uu____12963 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12911 FStar_List.unzip  in
            (match uu____12898 with
             | (pats,decls') ->
                 let uu____13143 = encode_formula body env2  in
                 (match uu____13143 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13175;
                             FStar_SMTEncoding_Term.rng = uu____13176;_}::[])::[]
                            when
                            let uu____13191 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13191 = gf -> []
                        | uu____13192 -> guards  in
                      let uu____13197 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13197, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      let uu____13206 = debug1 phi  in
      let phi1 = FStar_Syntax_Util.unascribe phi  in
      let check_pattern_vars vars pats =
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____13259  ->
                  match uu____13259 with
                  | (x,uu____13265) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv
                        x))
           in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____13273 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____13285 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____13285) uu____13273 tl1
               in
            let uu____13288 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____13315  ->
                      match uu____13315 with
                      | (b,uu____13321) ->
                          let uu____13322 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____13322))
               in
            (match uu____13288 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____13328) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____13342 =
                   let uu____13347 =
                     let uu____13348 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____13348
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____13347)
                    in
                 FStar_Errors.log_issue pos uu____13342)
         in
      let uu____13349 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
      match uu____13349 with
      | FStar_Pervasives_Native.None  -> fallback phi1
      | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
          ->
          let uu____13358 =
            FStar_All.pipe_right connectives
              (FStar_List.tryFind
                 (fun uu____13424  ->
                    match uu____13424 with
                    | (l,uu____13438) -> FStar_Ident.lid_equals op l))
             in
          (match uu____13358 with
           | FStar_Pervasives_Native.None  -> fallback phi1
           | FStar_Pervasives_Native.Some (uu____13477,f) ->
               f phi1.FStar_Syntax_Syntax.pos arms)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
          (vars,pats,body)) ->
          let uu____13516 =
            FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars))
             in
          let uu____13523 = encode_q_body env vars pats body  in
          (match uu____13523 with
           | (vars1,pats1,guard,body1,decls) ->
               let tm =
                 let uu____13568 =
                   let uu____13579 =
                     FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                   (pats1, vars1, uu____13579)  in
                 FStar_SMTEncoding_Term.mkForall uu____13568
                   phi1.FStar_Syntax_Syntax.pos
                  in
               (tm, decls))
      | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars,pats,body))
          ->
          let uu____13591 =
            FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars))
             in
          let uu____13598 = encode_q_body env vars pats body  in
          (match uu____13598 with
           | (vars1,pats1,guard,body1,decls) ->
               let uu____13642 =
                 let uu____13643 =
                   let uu____13654 =
                     FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                   (pats1, vars1, uu____13654)  in
                 FStar_SMTEncoding_Term.mkExists uu____13643
                   phi1.FStar_Syntax_Syntax.pos
                  in
               (uu____13642, decls))

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
  let uu____13776 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13776 with
  | (asym,a) ->
      let uu____13783 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13783 with
       | (xsym,x) ->
           let uu____13790 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13790 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13842 =
                      let uu____13853 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13853, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13842  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13879 =
                      let uu____13886 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13886)  in
                    FStar_SMTEncoding_Util.mkApp uu____13879  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13899 =
                    let uu____13902 =
                      let uu____13905 =
                        let uu____13908 =
                          let uu____13909 =
                            let uu____13916 =
                              let uu____13917 =
                                let uu____13928 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13928)  in
                              FStar_SMTEncoding_Util.mkForall uu____13917  in
                            (uu____13916, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13909  in
                        let uu____13945 =
                          let uu____13948 =
                            let uu____13949 =
                              let uu____13956 =
                                let uu____13957 =
                                  let uu____13968 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13968)  in
                                FStar_SMTEncoding_Util.mkForall uu____13957
                                 in
                              (uu____13956,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13949  in
                          [uu____13948]  in
                        uu____13908 :: uu____13945  in
                      xtok_decl :: uu____13905  in
                    xname_decl :: uu____13902  in
                  (xtok1, (FStar_List.length vars), uu____13899)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____14066 =
                    let uu____14082 =
                      let uu____14094 =
                        let uu____14095 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____14095
                         in
                      quant axy uu____14094  in
                    (FStar_Parser_Const.op_Eq, uu____14082)  in
                  let uu____14107 =
                    let uu____14125 =
                      let uu____14141 =
                        let uu____14153 =
                          let uu____14154 =
                            let uu____14155 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____14155  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____14154
                           in
                        quant axy uu____14153  in
                      (FStar_Parser_Const.op_notEq, uu____14141)  in
                    let uu____14167 =
                      let uu____14185 =
                        let uu____14201 =
                          let uu____14213 =
                            let uu____14214 =
                              let uu____14215 =
                                let uu____14220 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____14221 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____14220, uu____14221)  in
                              FStar_SMTEncoding_Util.mkLT uu____14215  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____14214
                             in
                          quant xy uu____14213  in
                        (FStar_Parser_Const.op_LT, uu____14201)  in
                      let uu____14233 =
                        let uu____14251 =
                          let uu____14267 =
                            let uu____14279 =
                              let uu____14280 =
                                let uu____14281 =
                                  let uu____14286 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____14287 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____14286, uu____14287)  in
                                FStar_SMTEncoding_Util.mkLTE uu____14281  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14280
                               in
                            quant xy uu____14279  in
                          (FStar_Parser_Const.op_LTE, uu____14267)  in
                        let uu____14299 =
                          let uu____14317 =
                            let uu____14333 =
                              let uu____14345 =
                                let uu____14346 =
                                  let uu____14347 =
                                    let uu____14352 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____14353 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____14352, uu____14353)  in
                                  FStar_SMTEncoding_Util.mkGT uu____14347  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14346
                                 in
                              quant xy uu____14345  in
                            (FStar_Parser_Const.op_GT, uu____14333)  in
                          let uu____14365 =
                            let uu____14383 =
                              let uu____14399 =
                                let uu____14411 =
                                  let uu____14412 =
                                    let uu____14413 =
                                      let uu____14418 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____14419 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____14418, uu____14419)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____14413
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14412
                                   in
                                quant xy uu____14411  in
                              (FStar_Parser_Const.op_GTE, uu____14399)  in
                            let uu____14431 =
                              let uu____14449 =
                                let uu____14465 =
                                  let uu____14477 =
                                    let uu____14478 =
                                      let uu____14479 =
                                        let uu____14484 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____14485 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____14484, uu____14485)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14479
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14478
                                     in
                                  quant xy uu____14477  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14465)
                                 in
                              let uu____14497 =
                                let uu____14515 =
                                  let uu____14531 =
                                    let uu____14543 =
                                      let uu____14544 =
                                        let uu____14545 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14545
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14544
                                       in
                                    quant qx uu____14543  in
                                  (FStar_Parser_Const.op_Minus, uu____14531)
                                   in
                                let uu____14557 =
                                  let uu____14575 =
                                    let uu____14591 =
                                      let uu____14603 =
                                        let uu____14604 =
                                          let uu____14605 =
                                            let uu____14610 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14611 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14610, uu____14611)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14605
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14604
                                         in
                                      quant xy uu____14603  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14591)
                                     in
                                  let uu____14623 =
                                    let uu____14641 =
                                      let uu____14657 =
                                        let uu____14669 =
                                          let uu____14670 =
                                            let uu____14671 =
                                              let uu____14676 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14677 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14676, uu____14677)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14671
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14670
                                           in
                                        quant xy uu____14669  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14657)
                                       in
                                    let uu____14689 =
                                      let uu____14707 =
                                        let uu____14723 =
                                          let uu____14735 =
                                            let uu____14736 =
                                              let uu____14737 =
                                                let uu____14742 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14743 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14742, uu____14743)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14737
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14736
                                             in
                                          quant xy uu____14735  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14723)
                                         in
                                      let uu____14755 =
                                        let uu____14773 =
                                          let uu____14789 =
                                            let uu____14801 =
                                              let uu____14802 =
                                                let uu____14803 =
                                                  let uu____14808 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14809 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14808, uu____14809)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14803
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14802
                                               in
                                            quant xy uu____14801  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14789)
                                           in
                                        let uu____14821 =
                                          let uu____14839 =
                                            let uu____14855 =
                                              let uu____14867 =
                                                let uu____14868 =
                                                  let uu____14869 =
                                                    let uu____14874 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____14875 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____14874,
                                                      uu____14875)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14869
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14868
                                                 in
                                              quant xy uu____14867  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14855)
                                             in
                                          let uu____14887 =
                                            let uu____14905 =
                                              let uu____14921 =
                                                let uu____14933 =
                                                  let uu____14934 =
                                                    let uu____14935 =
                                                      let uu____14940 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14941 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14940,
                                                        uu____14941)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14935
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14934
                                                   in
                                                quant xy uu____14933  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14921)
                                               in
                                            let uu____14953 =
                                              let uu____14971 =
                                                let uu____14987 =
                                                  let uu____14999 =
                                                    let uu____15000 =
                                                      let uu____15001 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____15001
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____15000
                                                     in
                                                  quant qx uu____14999  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14987)
                                                 in
                                              [uu____14971]  in
                                            uu____14905 :: uu____14953  in
                                          uu____14839 :: uu____14887  in
                                        uu____14773 :: uu____14821  in
                                      uu____14707 :: uu____14755  in
                                    uu____14641 :: uu____14689  in
                                  uu____14575 :: uu____14623  in
                                uu____14515 :: uu____14557  in
                              uu____14449 :: uu____14497  in
                            uu____14383 :: uu____14431  in
                          uu____14317 :: uu____14365  in
                        uu____14251 :: uu____14299  in
                      uu____14185 :: uu____14233  in
                    uu____14125 :: uu____14167  in
                  uu____14066 :: uu____14107  in
                let mk1 l v1 =
                  let uu____15270 =
                    let uu____15281 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____15351  ->
                              match uu____15351 with
                              | (l',uu____15367) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____15281
                      (FStar_Option.map
                         (fun uu____15443  ->
                            match uu____15443 with | (uu____15466,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____15270 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15556  ->
                          match uu____15556 with
                          | (l',uu____15572) -> FStar_Ident.lid_equals l l'))
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
        let uu____15622 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____15622 with
        | (xxsym,xx) ->
            let uu____15629 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____15629 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____15639 =
                   let uu____15646 =
                     let uu____15647 =
                       let uu____15658 =
                         let uu____15659 =
                           let uu____15664 =
                             let uu____15665 =
                               let uu____15670 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____15670)  in
                             FStar_SMTEncoding_Util.mkEq uu____15665  in
                           (xx_has_type, uu____15664)  in
                         FStar_SMTEncoding_Util.mkImp uu____15659  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15658)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____15647  in
                   let uu____15695 =
                     let uu____15696 =
                       let uu____15697 =
                         let uu____15698 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____15698  in
                       Prims.strcat module_name uu____15697  in
                     varops.mk_unique uu____15696  in
                   (uu____15646, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15695)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____15639)
  
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
    let uu____15745 =
      let uu____15746 =
        let uu____15753 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____15753, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15746  in
    let uu____15756 =
      let uu____15759 =
        let uu____15760 =
          let uu____15767 =
            let uu____15768 =
              let uu____15779 =
                let uu____15780 =
                  let uu____15785 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15785)  in
                FStar_SMTEncoding_Util.mkImp uu____15780  in
              ([[typing_pred]], [xx], uu____15779)  in
            mkForall_fuel uu____15768  in
          (uu____15767, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15760  in
      [uu____15759]  in
    uu____15745 :: uu____15756  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15830 =
      let uu____15831 =
        let uu____15838 =
          let uu____15839 =
            let uu____15850 =
              let uu____15855 =
                let uu____15858 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15858]  in
              [uu____15855]  in
            let uu____15863 =
              let uu____15864 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15864 tt  in
            (uu____15850, [bb], uu____15863)  in
          FStar_SMTEncoding_Util.mkForall uu____15839  in
        (uu____15838, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15831  in
    let uu____15885 =
      let uu____15888 =
        let uu____15889 =
          let uu____15896 =
            let uu____15897 =
              let uu____15908 =
                let uu____15909 =
                  let uu____15914 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____15914)  in
                FStar_SMTEncoding_Util.mkImp uu____15909  in
              ([[typing_pred]], [xx], uu____15908)  in
            mkForall_fuel uu____15897  in
          (uu____15896, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15889  in
      [uu____15888]  in
    uu____15830 :: uu____15885  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15967 =
        let uu____15968 =
          let uu____15975 =
            let uu____15978 =
              let uu____15981 =
                let uu____15984 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15985 =
                  let uu____15988 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15988]  in
                uu____15984 :: uu____15985  in
              tt :: uu____15981  in
            tt :: uu____15978  in
          ("Prims.Precedes", uu____15975)  in
        FStar_SMTEncoding_Util.mkApp uu____15968  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15967  in
    let precedes_y_x =
      let uu____15992 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15992  in
    let uu____15995 =
      let uu____15996 =
        let uu____16003 =
          let uu____16004 =
            let uu____16015 =
              let uu____16020 =
                let uu____16023 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____16023]  in
              [uu____16020]  in
            let uu____16028 =
              let uu____16029 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16029 tt  in
            (uu____16015, [bb], uu____16028)  in
          FStar_SMTEncoding_Util.mkForall uu____16004  in
        (uu____16003, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15996  in
    let uu____16050 =
      let uu____16053 =
        let uu____16054 =
          let uu____16061 =
            let uu____16062 =
              let uu____16073 =
                let uu____16074 =
                  let uu____16079 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____16079)  in
                FStar_SMTEncoding_Util.mkImp uu____16074  in
              ([[typing_pred]], [xx], uu____16073)  in
            mkForall_fuel uu____16062  in
          (uu____16061, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16054  in
      let uu____16104 =
        let uu____16107 =
          let uu____16108 =
            let uu____16115 =
              let uu____16116 =
                let uu____16127 =
                  let uu____16128 =
                    let uu____16133 =
                      let uu____16134 =
                        let uu____16137 =
                          let uu____16140 =
                            let uu____16143 =
                              let uu____16144 =
                                let uu____16149 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____16150 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____16149, uu____16150)  in
                              FStar_SMTEncoding_Util.mkGT uu____16144  in
                            let uu____16151 =
                              let uu____16154 =
                                let uu____16155 =
                                  let uu____16160 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____16161 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____16160, uu____16161)  in
                                FStar_SMTEncoding_Util.mkGTE uu____16155  in
                              let uu____16162 =
                                let uu____16165 =
                                  let uu____16166 =
                                    let uu____16171 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____16172 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____16171, uu____16172)  in
                                  FStar_SMTEncoding_Util.mkLT uu____16166  in
                                [uu____16165]  in
                              uu____16154 :: uu____16162  in
                            uu____16143 :: uu____16151  in
                          typing_pred_y :: uu____16140  in
                        typing_pred :: uu____16137  in
                      FStar_SMTEncoding_Util.mk_and_l uu____16134  in
                    (uu____16133, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____16128  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____16127)
                 in
              mkForall_fuel uu____16116  in
            (uu____16115,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____16108  in
        [uu____16107]  in
      uu____16053 :: uu____16104  in
    uu____15995 :: uu____16050  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____16221 =
      let uu____16222 =
        let uu____16229 =
          let uu____16230 =
            let uu____16241 =
              let uu____16246 =
                let uu____16249 = FStar_SMTEncoding_Term.boxString b  in
                [uu____16249]  in
              [uu____16246]  in
            let uu____16254 =
              let uu____16255 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____16255 tt  in
            (uu____16241, [bb], uu____16254)  in
          FStar_SMTEncoding_Util.mkForall uu____16230  in
        (uu____16229, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16222  in
    let uu____16276 =
      let uu____16279 =
        let uu____16280 =
          let uu____16287 =
            let uu____16288 =
              let uu____16299 =
                let uu____16300 =
                  let uu____16305 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____16305)  in
                FStar_SMTEncoding_Util.mkImp uu____16300  in
              ([[typing_pred]], [xx], uu____16299)  in
            mkForall_fuel uu____16288  in
          (uu____16287, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____16280  in
      [uu____16279]  in
    uu____16221 :: uu____16276  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____16364 =
      let uu____16365 =
        let uu____16372 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____16372, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16365  in
    [uu____16364]  in
  let mk_and_interp env conj uu____16387 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16412 =
      let uu____16413 =
        let uu____16420 =
          let uu____16421 =
            let uu____16432 =
              let uu____16433 =
                let uu____16438 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____16438, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16433  in
            ([[l_and_a_b]], [aa; bb], uu____16432)  in
          FStar_SMTEncoding_Util.mkForall uu____16421  in
        (uu____16420, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16413  in
    [uu____16412]  in
  let mk_or_interp env disj uu____16479 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16504 =
      let uu____16505 =
        let uu____16512 =
          let uu____16513 =
            let uu____16524 =
              let uu____16525 =
                let uu____16530 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____16530, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16525  in
            ([[l_or_a_b]], [aa; bb], uu____16524)  in
          FStar_SMTEncoding_Util.mkForall uu____16513  in
        (uu____16512, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16505  in
    [uu____16504]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____16596 =
      let uu____16597 =
        let uu____16604 =
          let uu____16605 =
            let uu____16616 =
              let uu____16617 =
                let uu____16622 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16622, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16617  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16616)  in
          FStar_SMTEncoding_Util.mkForall uu____16605  in
        (uu____16604, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16597  in
    [uu____16596]  in
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
    let uu____16698 =
      let uu____16699 =
        let uu____16706 =
          let uu____16707 =
            let uu____16718 =
              let uu____16719 =
                let uu____16724 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____16724, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16719  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16718)  in
          FStar_SMTEncoding_Util.mkForall uu____16707  in
        (uu____16706, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16699  in
    [uu____16698]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16798 =
      let uu____16799 =
        let uu____16806 =
          let uu____16807 =
            let uu____16818 =
              let uu____16819 =
                let uu____16824 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16824, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16819  in
            ([[l_imp_a_b]], [aa; bb], uu____16818)  in
          FStar_SMTEncoding_Util.mkForall uu____16807  in
        (uu____16806, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16799  in
    [uu____16798]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16890 =
      let uu____16891 =
        let uu____16898 =
          let uu____16899 =
            let uu____16910 =
              let uu____16911 =
                let uu____16916 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16916, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16911  in
            ([[l_iff_a_b]], [aa; bb], uu____16910)  in
          FStar_SMTEncoding_Util.mkForall uu____16899  in
        (uu____16898, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16891  in
    [uu____16890]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____16971 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16971  in
    let uu____16974 =
      let uu____16975 =
        let uu____16982 =
          let uu____16983 =
            let uu____16994 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16994)  in
          FStar_SMTEncoding_Util.mkForall uu____16983  in
        (uu____16982, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16975  in
    [uu____16974]  in
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
      let uu____17057 =
        let uu____17064 =
          let uu____17067 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17067]  in
        ("Valid", uu____17064)  in
      FStar_SMTEncoding_Util.mkApp uu____17057  in
    let uu____17070 =
      let uu____17071 =
        let uu____17078 =
          let uu____17079 =
            let uu____17090 =
              let uu____17091 =
                let uu____17096 =
                  let uu____17097 =
                    let uu____17108 =
                      let uu____17113 =
                        let uu____17116 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17116]  in
                      [uu____17113]  in
                    let uu____17121 =
                      let uu____17122 =
                        let uu____17127 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17127, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17122  in
                    (uu____17108, [xx1], uu____17121)  in
                  FStar_SMTEncoding_Util.mkForall uu____17097  in
                (uu____17096, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17091  in
            ([[l_forall_a_b]], [aa; bb], uu____17090)  in
          FStar_SMTEncoding_Util.mkForall uu____17079  in
        (uu____17078, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17071  in
    [uu____17070]  in
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
      let uu____17212 =
        let uu____17219 =
          let uu____17222 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____17222]  in
        ("Valid", uu____17219)  in
      FStar_SMTEncoding_Util.mkApp uu____17212  in
    let uu____17225 =
      let uu____17226 =
        let uu____17233 =
          let uu____17234 =
            let uu____17245 =
              let uu____17246 =
                let uu____17251 =
                  let uu____17252 =
                    let uu____17263 =
                      let uu____17268 =
                        let uu____17271 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____17271]  in
                      [uu____17268]  in
                    let uu____17276 =
                      let uu____17277 =
                        let uu____17282 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____17282, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____17277  in
                    (uu____17263, [xx1], uu____17276)  in
                  FStar_SMTEncoding_Util.mkExists uu____17252  in
                (uu____17251, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____17246  in
            ([[l_exists_a_b]], [aa; bb], uu____17245)  in
          FStar_SMTEncoding_Util.mkForall uu____17234  in
        (uu____17233, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17226  in
    [uu____17225]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____17345 =
      let uu____17346 =
        let uu____17353 =
          let uu____17354 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____17354 range_ty  in
        let uu____17355 = varops.mk_unique "typing_range_const"  in
        (uu____17353, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____17355)
         in
      FStar_SMTEncoding_Util.mkAssume uu____17346  in
    [uu____17345]  in
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
        let uu____17392 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____17392 x1 t  in
      let uu____17393 =
        let uu____17404 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____17404)  in
      FStar_SMTEncoding_Util.mkForall uu____17393  in
    let uu____17427 =
      let uu____17428 =
        let uu____17435 =
          let uu____17436 =
            let uu____17447 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____17447)  in
          FStar_SMTEncoding_Util.mkForall uu____17436  in
        (uu____17435,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17428  in
    [uu____17427]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____17500 =
      let uu____17501 =
        let uu____17508 =
          let uu____17509 =
            let uu____17524 =
              let uu____17525 =
                let uu____17530 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____17531 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____17530, uu____17531)  in
              FStar_SMTEncoding_Util.mkAnd uu____17525  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____17524)
             in
          FStar_SMTEncoding_Util.mkForall' uu____17509  in
        (uu____17508,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____17501  in
    [uu____17500]  in
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
          let uu____17991 =
            FStar_Util.find_opt
              (fun uu____18023  ->
                 match uu____18023 with
                 | (l,uu____18035) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____17991 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____18069,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____18120 = encode_function_type_as_formula t env  in
        match uu____18120 with
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
              let uu____18172 =
                ((let uu____18175 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____18175) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____18172
              then
                let arg_sorts =
                  let uu____18185 =
                    let uu____18186 = FStar_Syntax_Subst.compress t_norm  in
                    uu____18186.FStar_Syntax_Syntax.n  in
                  match uu____18185 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____18192) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____18222  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____18227 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____18229 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____18229 with
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
                (let uu____18262 = prims.is lid  in
                 if uu____18262
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____18270 = prims.mk lid vname  in
                   match uu____18270 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____18297 =
                      let uu____18308 = curried_arrow_formals_comp t_norm  in
                      match uu____18308 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____18326 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____18326
                            then
                              let uu____18327 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___121_18330 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___121_18330.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___121_18330.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___121_18330.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___121_18330.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___121_18330.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___121_18330.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___121_18330.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___121_18330.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___121_18330.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___121_18330.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___121_18330.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___121_18330.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___121_18330.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___121_18330.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___121_18330.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___121_18330.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___121_18330.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___121_18330.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___121_18330.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___121_18330.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___121_18330.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___121_18330.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___121_18330.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___121_18330.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___121_18330.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___121_18330.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___121_18330.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___121_18330.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___121_18330.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___121_18330.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___121_18330.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___121_18330.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___121_18330.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___121_18330.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___121_18330.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___121_18330.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____18327
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____18342 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____18342)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____18297 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____18392 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____18392 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____18417 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___93_18463  ->
                                       match uu___93_18463 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____18467 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18467 with
                                            | (uu____18488,(xxsym,uu____18490))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____18508 =
                                                  let uu____18509 =
                                                    let uu____18516 =
                                                      let uu____18517 =
                                                        let uu____18528 =
                                                          let uu____18529 =
                                                            let uu____18534 =
                                                              let uu____18535
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____18535
                                                               in
                                                            (vapp,
                                                              uu____18534)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____18529
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18528)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18517
                                                       in
                                                    (uu____18516,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18509
                                                   in
                                                [uu____18508])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____18554 =
                                             FStar_Util.prefix vars  in
                                           (match uu____18554 with
                                            | (uu____18575,(xxsym,uu____18577))
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
                                                let uu____18600 =
                                                  let uu____18601 =
                                                    let uu____18608 =
                                                      let uu____18609 =
                                                        let uu____18620 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____18620)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____18609
                                                       in
                                                    (uu____18608,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____18601
                                                   in
                                                [uu____18600])
                                       | uu____18637 -> []))
                                in
                             let uu____18638 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____18638 with
                              | (vars,guards,env',decls1,uu____18665) ->
                                  let uu____18678 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____18687 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____18687, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____18689 =
                                          encode_formula p env'  in
                                        (match uu____18689 with
                                         | (g,ds) ->
                                             let uu____18700 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____18700,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____18678 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____18713 =
                                           let uu____18720 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____18720)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____18713
                                          in
                                       let uu____18729 =
                                         let vname_decl =
                                           let uu____18737 =
                                             let uu____18748 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____18758  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____18748,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____18737
                                            in
                                         let uu____18767 =
                                           let env2 =
                                             let uu___122_18773 = env1  in
                                             {
                                               bindings =
                                                 (uu___122_18773.bindings);
                                               depth = (uu___122_18773.depth);
                                               tcenv = (uu___122_18773.tcenv);
                                               warn = (uu___122_18773.warn);
                                               cache = (uu___122_18773.cache);
                                               nolabels =
                                                 (uu___122_18773.nolabels);
                                               use_zfuel_name =
                                                 (uu___122_18773.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___122_18773.current_module_name)
                                             }  in
                                           let uu____18774 =
                                             let uu____18775 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____18775
                                              in
                                           if uu____18774
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____18767 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____18790::uu____18791 ->
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
                                                     let uu____18831 =
                                                       let uu____18842 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____18842)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____18831
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____18869 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____18872 =
                                               match formals with
                                               | [] ->
                                                   let uu____18889 =
                                                     let uu____18890 =
                                                       let uu____18893 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____18893
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____18890
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____18889)
                                               | uu____18902 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____18909 =
                                                       let uu____18916 =
                                                         let uu____18917 =
                                                           let uu____18928 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____18928)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____18917
                                                          in
                                                       (uu____18916,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____18909
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____18872 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____18729 with
                                        | (decls2,env2) ->
                                            let uu____18971 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____18979 =
                                                encode_term res_t1 env'  in
                                              match uu____18979 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____18992 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____18992, decls)
                                               in
                                            (match uu____18971 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____19003 =
                                                     let uu____19010 =
                                                       let uu____19011 =
                                                         let uu____19022 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____19022)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____19011
                                                        in
                                                     (uu____19010,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____19003
                                                    in
                                                 let freshness =
                                                   let uu____19038 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____19038
                                                   then
                                                     let uu____19043 =
                                                       let uu____19044 =
                                                         let uu____19055 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____19066 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____19055,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____19066)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____19044
                                                        in
                                                     let uu____19069 =
                                                       let uu____19072 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____19072]  in
                                                     uu____19043 ::
                                                       uu____19069
                                                   else []  in
                                                 let g =
                                                   let uu____19077 =
                                                     let uu____19080 =
                                                       let uu____19083 =
                                                         let uu____19086 =
                                                           let uu____19089 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____19089
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____19086
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____19083
                                                        in
                                                     FStar_List.append decls2
                                                       uu____19080
                                                      in
                                                   FStar_List.append decls11
                                                     uu____19077
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
          let uu____19122 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____19122 with
          | FStar_Pervasives_Native.None  ->
              let uu____19133 = encode_free_var false env x t t_norm []  in
              (match uu____19133 with
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
            let uu____19196 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____19196 with
            | (decls,env1) ->
                let uu____19215 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____19215
                then
                  let uu____19222 =
                    let uu____19225 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____19225  in
                  (uu____19222, env1)
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
             (fun uu____19283  ->
                fun lb  ->
                  match uu____19283 with
                  | (decls,env1) ->
                      let uu____19303 =
                        let uu____19310 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____19310
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____19303 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____19333 = FStar_Syntax_Util.head_and_args t  in
    match uu____19333 with
    | (hd1,args) ->
        let uu____19370 =
          let uu____19371 = FStar_Syntax_Util.un_uinst hd1  in
          uu____19371.FStar_Syntax_Syntax.n  in
        (match uu____19370 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____19375,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____19394 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____19422  ->
      fun quals  ->
        match uu____19422 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____19502 = FStar_Util.first_N nbinders formals  in
              match uu____19502 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____19583  ->
                         fun uu____19584  ->
                           match (uu____19583, uu____19584) with
                           | ((formal,uu____19602),(binder,uu____19604)) ->
                               let uu____19613 =
                                 let uu____19620 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____19620)  in
                               FStar_Syntax_Syntax.NT uu____19613) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____19628 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____19659  ->
                              match uu____19659 with
                              | (x,i) ->
                                  let uu____19670 =
                                    let uu___123_19671 = x  in
                                    let uu____19672 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___123_19671.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___123_19671.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____19672
                                    }  in
                                  (uu____19670, i)))
                       in
                    FStar_All.pipe_right uu____19628
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____19690 =
                      let uu____19693 = FStar_Syntax_Subst.compress body  in
                      let uu____19694 =
                        let uu____19695 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____19695
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____19693
                        uu____19694
                       in
                    uu____19690 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____19760 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____19760
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___124_19763 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___124_19763.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___124_19763.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___124_19763.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___124_19763.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___124_19763.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___124_19763.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___124_19763.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___124_19763.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___124_19763.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___124_19763.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___124_19763.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___124_19763.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___124_19763.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___124_19763.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___124_19763.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___124_19763.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___124_19763.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___124_19763.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___124_19763.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___124_19763.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___124_19763.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___124_19763.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___124_19763.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___124_19763.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___124_19763.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___124_19763.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___124_19763.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___124_19763.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___124_19763.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___124_19763.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___124_19763.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___124_19763.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___124_19763.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___124_19763.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___124_19763.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___124_19763.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____19798 = FStar_Syntax_Util.abs_formals e  in
                match uu____19798 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____19862::uu____19863 ->
                         let uu____19878 =
                           let uu____19879 =
                             let uu____19882 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____19882
                              in
                           uu____19879.FStar_Syntax_Syntax.n  in
                         (match uu____19878 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19925 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____19925 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____19967 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____19967
                                   then
                                     let uu____20002 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____20002 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____20096  ->
                                                   fun uu____20097  ->
                                                     match (uu____20096,
                                                             uu____20097)
                                                     with
                                                     | ((x,uu____20115),
                                                        (b,uu____20117)) ->
                                                         let uu____20126 =
                                                           let uu____20133 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____20133)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____20126)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____20135 =
                                            let uu____20156 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____20156)
                                             in
                                          (uu____20135, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____20224 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____20224 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____20313) ->
                              let uu____20318 =
                                let uu____20339 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____20339  in
                              (uu____20318, true)
                          | uu____20404 when Prims.op_Negation norm1 ->
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
                          | uu____20406 ->
                              let uu____20407 =
                                let uu____20408 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____20409 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____20408
                                  uu____20409
                                 in
                              failwith uu____20407)
                     | uu____20434 ->
                         let rec aux' t_norm2 =
                           let uu____20460 =
                             let uu____20461 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____20461.FStar_Syntax_Syntax.n  in
                           match uu____20460 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____20502 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____20502 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____20530 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____20530 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____20610)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____20615 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____20671 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____20671
               then encode_top_level_vals env bindings quals
               else
                 (let uu____20683 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____20746  ->
                            fun lb  ->
                              match uu____20746 with
                              | (toks,typs,decls,env1) ->
                                  let uu____20800 =
                                    let uu____20801 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____20801
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ()  in
                                  let t_norm =
                                    whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                     in
                                  let uu____20804 =
                                    let uu____20813 =
                                      FStar_Util.right
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    declare_top_level_let env1 uu____20813
                                      lb.FStar_Syntax_Syntax.lbtyp t_norm
                                     in
                                  (match uu____20804 with
                                   | (tok,decl,env2) ->
                                       ((tok :: toks), (t_norm :: typs),
                                         (decl :: decls), env2)))
                         ([], [], [], env))
                     in
                  match uu____20683 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____20933 =
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
                        | uu____20939 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20947 = mk_fv ()  in
                                   mk_Apply uu____20947 vars)
                            else
                              (let uu____20949 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____20949)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____21005;
                             FStar_Syntax_Syntax.lbeff = uu____21006;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____21008;
                             FStar_Syntax_Syntax.lbpos = uu____21009;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____21033 =
                              let uu____21040 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____21040 with
                              | (tcenv',uu____21058,e_t) ->
                                  let uu____21064 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____21075 -> failwith "Impossible"
                                     in
                                  (match uu____21064 with
                                   | (e1,t_norm1) ->
                                       ((let uu___127_21091 = env2  in
                                         {
                                           bindings =
                                             (uu___127_21091.bindings);
                                           depth = (uu___127_21091.depth);
                                           tcenv = tcenv';
                                           warn = (uu___127_21091.warn);
                                           cache = (uu___127_21091.cache);
                                           nolabels =
                                             (uu___127_21091.nolabels);
                                           use_zfuel_name =
                                             (uu___127_21091.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___127_21091.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___127_21091.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____21033 with
                             | (env',e1,t_norm1) ->
                                 let uu____21101 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____21101 with
                                  | ((binders,body,uu____21122,t_body),curry)
                                      ->
                                      let uu____21133 =
                                        let uu____21134 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____21134
                                        then
                                          let uu____21135 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____21136 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____21135 uu____21136
                                        else ()  in
                                      let uu____21138 =
                                        encode_binders
                                          FStar_Pervasives_Native.None
                                          binders env'
                                         in
                                      (match uu____21138 with
                                       | (vars,guards,env'1,binder_decls,uu____21165)
                                           ->
                                           let body1 =
                                             let uu____21179 =
                                               FStar_TypeChecker_Env.is_reifiable_function
                                                 env'1.tcenv t_norm1
                                                in
                                             if uu____21179
                                             then
                                               FStar_TypeChecker_Util.reify_body
                                                 env'1.tcenv body
                                             else
                                               FStar_Syntax_Util.ascribe body
                                                 ((FStar_Util.Inl t_body),
                                                   FStar_Pervasives_Native.None)
                                              in
                                           let app =
                                             let uu____21196 =
                                               FStar_Syntax_Util.range_of_lbname
                                                 lbn
                                                in
                                             mk_app1 uu____21196 curry fvb
                                               vars
                                              in
                                           let uu____21197 =
                                             let uu____21206 =
                                               FStar_All.pipe_right quals
                                                 (FStar_List.contains
                                                    FStar_Syntax_Syntax.Logic)
                                                in
                                             if uu____21206
                                             then
                                               let uu____21217 =
                                                 FStar_SMTEncoding_Term.mk_Valid
                                                   app
                                                  in
                                               let uu____21218 =
                                                 encode_formula body1 env'1
                                                  in
                                               (uu____21217, uu____21218)
                                             else
                                               (let uu____21228 =
                                                  encode_term body1 env'1  in
                                                (app, uu____21228))
                                              in
                                           (match uu____21197 with
                                            | (app1,(body2,decls2)) ->
                                                let eqn =
                                                  let uu____21251 =
                                                    let uu____21258 =
                                                      let uu____21259 =
                                                        let uu____21270 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app1, body2)
                                                           in
                                                        ([[app1]], vars,
                                                          uu____21270)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____21259
                                                       in
                                                    let uu____21281 =
                                                      let uu____21284 =
                                                        FStar_Util.format1
                                                          "Equation for %s"
                                                          flid.FStar_Ident.str
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____21284
                                                       in
                                                    (uu____21258,
                                                      uu____21281,
                                                      (Prims.strcat
                                                         "equation_"
                                                         fvb.smt_id))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____21251
                                                   in
                                                let uu____21287 =
                                                  let uu____21290 =
                                                    let uu____21293 =
                                                      let uu____21296 =
                                                        let uu____21299 =
                                                          primitive_type_axioms
                                                            env2.tcenv flid
                                                            fvb.smt_id app1
                                                           in
                                                        FStar_List.append
                                                          [eqn] uu____21299
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____21296
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____21293
                                                     in
                                                  FStar_List.append decls1
                                                    uu____21290
                                                   in
                                                (uu____21287, env2)))))
                        | uu____21304 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____21363 = varops.fresh "fuel"  in
                          (uu____21363, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____21366 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____21413  ->
                                  fun fvb  ->
                                    match uu____21413 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____21459 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____21459  in
                                        let gtok =
                                          let uu____21461 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____21461  in
                                        let env4 =
                                          let uu____21463 =
                                            let uu____21466 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____21466
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____21463
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____21366 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21570 t_norm
                              uu____21572 =
                              match (uu____21570, uu____21572) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____21602;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____21603;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____21605;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____21606;_})
                                  ->
                                  let uu____21627 =
                                    let uu____21634 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21634 with
                                    | (tcenv',uu____21656,e_t) ->
                                        let uu____21662 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21673 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21662 with
                                         | (e1,t_norm1) ->
                                             ((let uu___128_21689 = env3  in
                                               {
                                                 bindings =
                                                   (uu___128_21689.bindings);
                                                 depth =
                                                   (uu___128_21689.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___128_21689.warn);
                                                 cache =
                                                   (uu___128_21689.cache);
                                                 nolabels =
                                                   (uu___128_21689.nolabels);
                                                 use_zfuel_name =
                                                   (uu___128_21689.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___128_21689.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___128_21689.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21627 with
                                   | (env',e1,t_norm1) ->
                                       let uu____21703 =
                                         let uu____21704 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21704
                                         then
                                           let uu____21705 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21706 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21707 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21705 uu____21706
                                             uu____21707
                                         else ()  in
                                       let uu____21709 =
                                         destruct_bound_function fvb.fvar_lid
                                           t_norm1 e1
                                          in
                                       (match uu____21709 with
                                        | ((binders,body,formals,tres),curry)
                                            ->
                                            let uu____21745 =
                                              let uu____21746 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env01.tcenv)
                                                  (FStar_Options.Other
                                                     "SMTEncoding")
                                                 in
                                              if uu____21746
                                              then
                                                let uu____21747 =
                                                  FStar_Syntax_Print.binders_to_string
                                                    ", " binders
                                                   in
                                                let uu____21748 =
                                                  FStar_Syntax_Print.term_to_string
                                                    body
                                                   in
                                                let uu____21749 =
                                                  FStar_Syntax_Print.binders_to_string
                                                    ", " formals
                                                   in
                                                let uu____21750 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tres
                                                   in
                                                FStar_Util.print4
                                                  "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                  uu____21747 uu____21748
                                                  uu____21749 uu____21750
                                              else ()  in
                                            let uu____21752 =
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ()  in
                                            let uu____21754 =
                                              encode_binders
                                                FStar_Pervasives_Native.None
                                                binders env'
                                               in
                                            (match uu____21754 with
                                             | (vars,guards,env'1,binder_decls,uu____21785)
                                                 ->
                                                 let decl_g =
                                                   let uu____21799 =
                                                     let uu____21810 =
                                                       let uu____21813 =
                                                         FStar_List.map
                                                           FStar_Pervasives_Native.snd
                                                           vars
                                                          in
                                                       FStar_SMTEncoding_Term.Fuel_sort
                                                         :: uu____21813
                                                        in
                                                     (g, uu____21810,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       (FStar_Pervasives_Native.Some
                                                          "Fuel-instrumented function name"))
                                                      in
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     uu____21799
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
                                                   let uu____21838 =
                                                     let uu____21845 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         vars
                                                        in
                                                     ((fvb.smt_id),
                                                       uu____21845)
                                                      in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____21838
                                                    in
                                                 let gsapp =
                                                   let uu____21855 =
                                                     let uu____21862 =
                                                       let uu____21865 =
                                                         FStar_SMTEncoding_Util.mkApp
                                                           ("SFuel",
                                                             [fuel_tm])
                                                          in
                                                       uu____21865 :: vars_tm
                                                        in
                                                     (g, uu____21862)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____21855
                                                    in
                                                 let gmax =
                                                   let uu____21871 =
                                                     let uu____21878 =
                                                       let uu____21881 =
                                                         FStar_SMTEncoding_Util.mkApp
                                                           ("MaxFuel", [])
                                                          in
                                                       uu____21881 :: vars_tm
                                                        in
                                                     (g, uu____21878)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____21871
                                                    in
                                                 let body1 =
                                                   let uu____21887 =
                                                     FStar_TypeChecker_Env.is_reifiable_function
                                                       env'1.tcenv t_norm1
                                                      in
                                                   if uu____21887
                                                   then
                                                     FStar_TypeChecker_Util.reify_body
                                                       env'1.tcenv body
                                                   else body  in
                                                 let uu____21889 =
                                                   encode_term body1 env'1
                                                    in
                                                 (match uu____21889 with
                                                  | (body_tm,decls2) ->
                                                      let eqn_g =
                                                        let uu____21907 =
                                                          let uu____21914 =
                                                            let uu____21915 =
                                                              let uu____21930
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
                                                                uu____21930)
                                                               in
                                                            FStar_SMTEncoding_Util.mkForall'
                                                              uu____21915
                                                             in
                                                          let uu____21951 =
                                                            let uu____21954 =
                                                              FStar_Util.format1
                                                                "Equation for fuel-instrumented recursive function: %s"
                                                                (fvb.fvar_lid).FStar_Ident.str
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____21954
                                                             in
                                                          (uu____21914,
                                                            uu____21951,
                                                            (Prims.strcat
                                                               "equation_with_fuel_"
                                                               g))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____21907
                                                         in
                                                      let eqn_f =
                                                        let uu____21958 =
                                                          let uu____21965 =
                                                            let uu____21966 =
                                                              let uu____21977
                                                                =
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  (app, gmax)
                                                                 in
                                                              ([[app]], vars,
                                                                uu____21977)
                                                               in
                                                            FStar_SMTEncoding_Util.mkForall
                                                              uu____21966
                                                             in
                                                          (uu____21965,
                                                            (FStar_Pervasives_Native.Some
                                                               "Correspondence of recursive function to instrumented version"),
                                                            (Prims.strcat
                                                               "@fuel_correspondence_"
                                                               g))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____21958
                                                         in
                                                      let eqn_g' =
                                                        let uu____21991 =
                                                          let uu____21998 =
                                                            let uu____21999 =
                                                              let uu____22010
                                                                =
                                                                let uu____22011
                                                                  =
                                                                  let uu____22016
                                                                    =
                                                                    let uu____22017
                                                                    =
                                                                    let uu____22024
                                                                    =
                                                                    let uu____22027
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____22027
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____22024)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____22017
                                                                     in
                                                                  (gsapp,
                                                                    uu____22016)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____22011
                                                                 in
                                                              ([[gsapp]],
                                                                (fuel ::
                                                                vars),
                                                                uu____22010)
                                                               in
                                                            FStar_SMTEncoding_Util.mkForall
                                                              uu____21999
                                                             in
                                                          (uu____21998,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel irrelevance"),
                                                            (Prims.strcat
                                                               "@fuel_irrelevance_"
                                                               g))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____21991
                                                         in
                                                      let uu____22050 =
                                                        let uu____22059 =
                                                          encode_binders
                                                            FStar_Pervasives_Native.None
                                                            formals env02
                                                           in
                                                        match uu____22059
                                                        with
                                                        | (vars1,v_guards,env4,binder_decls1,uu____22088)
                                                            ->
                                                            let vars_tm1 =
                                                              FStar_List.map
                                                                FStar_SMTEncoding_Util.mkFreeV
                                                                vars1
                                                               in
                                                            let gapp =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (g, (fuel_tm
                                                                  ::
                                                                  vars_tm1))
                                                               in
                                                            let tok_corr =
                                                              let tok_app =
                                                                let uu____22113
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                   in
                                                                mk_Apply
                                                                  uu____22113
                                                                  (fuel ::
                                                                  vars1)
                                                                 in
                                                              let uu____22118
                                                                =
                                                                let uu____22125
                                                                  =
                                                                  let uu____22126
                                                                    =
                                                                    let uu____22137
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22137)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkForall
                                                                    uu____22126
                                                                   in
                                                                (uu____22125,
                                                                  (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                  (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                 in
                                                              FStar_SMTEncoding_Util.mkAssume
                                                                uu____22118
                                                               in
                                                            let uu____22158 =
                                                              let uu____22165
                                                                =
                                                                encode_term_pred
                                                                  FStar_Pervasives_Native.None
                                                                  tres env4
                                                                  gapp
                                                                 in
                                                              match uu____22165
                                                              with
                                                              | (g_typing,d3)
                                                                  ->
                                                                  let uu____22178
                                                                    =
                                                                    let uu____22181
                                                                    =
                                                                    let uu____22182
                                                                    =
                                                                    let uu____22189
                                                                    =
                                                                    let uu____22190
                                                                    =
                                                                    let uu____22201
                                                                    =
                                                                    let uu____22202
                                                                    =
                                                                    let uu____22207
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____22207,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____22202
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____22201)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____22190
                                                                     in
                                                                    (uu____22189,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____22182
                                                                     in
                                                                    [uu____22181]
                                                                     in
                                                                  (d3,
                                                                    uu____22178)
                                                               in
                                                            (match uu____22158
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
                                                      (match uu____22050 with
                                                       | (aux_decls,g_typing)
                                                           ->
                                                           ((FStar_List.append
                                                               binder_decls
                                                               (FStar_List.append
                                                                  decls2
                                                                  (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                             (FStar_List.append
                                                                [eqn_g;
                                                                eqn_g';
                                                                eqn_f]
                                                                g_typing),
                                                             env02))))))
                               in
                            let uu____22272 =
                              let uu____22285 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____22346  ->
                                   fun uu____22347  ->
                                     match (uu____22346, uu____22347) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22472 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____22472 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____22285
                               in
                            (match uu____22272 with
                             | (decls2,eqns,env01) ->
                                 let uu____22545 =
                                   let isDeclFun uu___94_22558 =
                                     match uu___94_22558 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22559 -> true
                                     | uu____22570 -> false  in
                                   let uu____22571 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22571
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22545 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22611 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___95_22615  ->
                                 match uu___95_22615 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22616 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22622 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22622)))
                         in
                      if uu____22611
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
                   let uu____22674 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22674
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
        let uu____22735 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22735 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22739 = encode_sigelt' env se  in
      match uu____22739 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22755 =
                  let uu____22756 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22756  in
                [uu____22755]
            | uu____22757 ->
                let uu____22758 =
                  let uu____22761 =
                    let uu____22762 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22762  in
                  uu____22761 :: g  in
                let uu____22763 =
                  let uu____22766 =
                    let uu____22767 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22767  in
                  [uu____22766]  in
                FStar_List.append uu____22758 uu____22763
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
        let uu____22781 =
          let uu____22782 = FStar_Syntax_Subst.compress t  in
          uu____22782.FStar_Syntax_Syntax.n  in
        match uu____22781 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22786)) -> s = "opaque_to_smt"
        | uu____22787 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22793 =
          let uu____22794 = FStar_Syntax_Subst.compress t  in
          uu____22794.FStar_Syntax_Syntax.n  in
        match uu____22793 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22798)) -> s = "uninterpreted_by_smt"
        | uu____22799 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22804 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____22809 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22820 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22823 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22826 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22841 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22845 =
            let uu____22846 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____22846 Prims.op_Negation  in
          if uu____22845
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22873 ->
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
               let uu____22895 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____22895 with
               | (formals,uu____22913) ->
                   let arity = FStar_List.length formals  in
                   let uu____22931 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____22931 with
                    | (aname,atok,env2) ->
                        let uu____22951 =
                          let uu____22956 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____22956 env2  in
                        (match uu____22951 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22968 =
                                 let uu____22969 =
                                   let uu____22980 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22996  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____22980,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____22969
                                  in
                               [uu____22968;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____23009 =
                               let aux uu____23063 uu____23064 =
                                 match (uu____23063, uu____23064) with
                                 | ((bv,uu____23116),(env3,acc_sorts,acc)) ->
                                     let uu____23154 = gen_term_var env3 bv
                                        in
                                     (match uu____23154 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____23009 with
                              | (uu____23226,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____23249 =
                                      let uu____23256 =
                                        let uu____23257 =
                                          let uu____23268 =
                                            let uu____23269 =
                                              let uu____23274 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____23274)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23269
                                             in
                                          ([[app]], xs_sorts, uu____23268)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23257
                                         in
                                      (uu____23256,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23249
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____23294 =
                                      let uu____23301 =
                                        let uu____23302 =
                                          let uu____23313 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____23313)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23302
                                         in
                                      (uu____23301,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23294
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____23332 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____23332 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23360,uu____23361)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23362 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____23362 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23379,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____23385 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___96_23389  ->
                      match uu___96_23389 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23390 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23395 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23396 -> false))
               in
            Prims.op_Negation uu____23385  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____23405 =
               let uu____23412 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____23412 env fv t quals  in
             match uu____23405 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____23427 =
                   let uu____23430 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____23430  in
                 (uu____23427, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23438 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____23438 with
           | (uu____23447,f1) ->
               let uu____23449 = encode_formula f1 env  in
               (match uu____23449 with
                | (f2,decls) ->
                    let g =
                      let uu____23463 =
                        let uu____23464 =
                          let uu____23471 =
                            let uu____23474 =
                              let uu____23475 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____23475
                               in
                            FStar_Pervasives_Native.Some uu____23474  in
                          let uu____23476 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____23471, uu____23476)  in
                        FStar_SMTEncoding_Util.mkAssume uu____23464  in
                      [uu____23463]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23482) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____23494 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23512 =
                       let uu____23515 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____23515.FStar_Syntax_Syntax.fv_name  in
                     uu____23512.FStar_Syntax_Syntax.v  in
                   let uu____23516 =
                     let uu____23517 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____23517  in
                   if uu____23516
                   then
                     let val_decl =
                       let uu___131_23545 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___131_23545.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___131_23545.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___131_23545.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23550 = encode_sigelt' env1 val_decl  in
                     match uu____23550 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____23494 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23578,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23580;
                          FStar_Syntax_Syntax.lbtyp = uu____23581;
                          FStar_Syntax_Syntax.lbeff = uu____23582;
                          FStar_Syntax_Syntax.lbdef = uu____23583;
                          FStar_Syntax_Syntax.lbattrs = uu____23584;
                          FStar_Syntax_Syntax.lbpos = uu____23585;_}::[]),uu____23586)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23609 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____23609 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23638 =
                   let uu____23641 =
                     let uu____23642 =
                       let uu____23649 =
                         let uu____23650 =
                           let uu____23661 =
                             let uu____23662 =
                               let uu____23667 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23667)  in
                             FStar_SMTEncoding_Util.mkEq uu____23662  in
                           ([[b2t_x]], [xx], uu____23661)  in
                         FStar_SMTEncoding_Util.mkForall uu____23650  in
                       (uu____23649,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23642  in
                   [uu____23641]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23638
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23700,uu____23701) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_23710  ->
                  match uu___97_23710 with
                  | FStar_Syntax_Syntax.Discriminator uu____23711 -> true
                  | uu____23712 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23715,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23726 =
                     let uu____23727 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23727.FStar_Ident.idText  in
                   uu____23726 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___98_23731  ->
                     match uu___98_23731 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23732 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23736) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___99_23753  ->
                  match uu___99_23753 with
                  | FStar_Syntax_Syntax.Projector uu____23754 -> true
                  | uu____23759 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23762 = try_lookup_free_var env l  in
          (match uu____23762 with
           | FStar_Pervasives_Native.Some uu____23769 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___132_23773 = se  in
                 let uu____23774 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____23774;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___132_23773.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___132_23773.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___132_23773.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23781) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23799) ->
          let uu____23808 = encode_sigelts env ses  in
          (match uu____23808 with
           | (g,env1) ->
               let uu____23825 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___100_23848  ->
                         match uu___100_23848 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23849;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23850;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23851;_}
                             -> false
                         | uu____23854 -> true))
                  in
               (match uu____23825 with
                | (g',inversions) ->
                    let uu____23869 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___101_23890  ->
                              match uu___101_23890 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23891 ->
                                  true
                              | uu____23902 -> false))
                       in
                    (match uu____23869 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23920,tps,k,uu____23923,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___102_23940  ->
                    match uu___102_23940 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23941 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23951 = c  in
              match uu____23951 with
              | (name,args,uu____23956,uu____23957,uu____23958) ->
                  let uu____23963 =
                    let uu____23964 =
                      let uu____23975 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23992  ->
                                match uu____23992 with
                                | (uu____23999,sort,uu____24001) -> sort))
                         in
                      (name, uu____23975, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____23964  in
                  [uu____23963]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____24030 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____24036 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____24036 FStar_Option.isNone))
               in
            if uu____24030
            then []
            else
              (let uu____24068 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____24068 with
               | (xxsym,xx) ->
                   let uu____24077 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____24116  ->
                             fun l  ->
                               match uu____24116 with
                               | (out,decls) ->
                                   let uu____24136 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____24136 with
                                    | (uu____24147,data_t) ->
                                        let uu____24149 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____24149 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____24195 =
                                                 let uu____24196 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____24196.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____24195 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____24207,indices) ->
                                                   indices
                                               | uu____24229 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24253  ->
                                                         match uu____24253
                                                         with
                                                         | (x,uu____24259) ->
                                                             let uu____24260
                                                               =
                                                               let uu____24261
                                                                 =
                                                                 let uu____24268
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____24268,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24261
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____24260)
                                                    env)
                                                in
                                             let uu____24271 =
                                               encode_args indices env1  in
                                             (match uu____24271 with
                                              | (indices1,decls') ->
                                                  let uu____24290 =
                                                    if
                                                      (FStar_List.length
                                                         indices1)
                                                        <>
                                                        (FStar_List.length
                                                           vars)
                                                    then
                                                      failwith "Impossible"
                                                    else ()  in
                                                  let eqs =
                                                    let uu____24297 =
                                                      FStar_List.map2
                                                        (fun v1  ->
                                                           fun a  ->
                                                             let uu____24313
                                                               =
                                                               let uu____24318
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkFreeV
                                                                   v1
                                                                  in
                                                               (uu____24318,
                                                                 a)
                                                                in
                                                             FStar_SMTEncoding_Util.mkEq
                                                               uu____24313)
                                                        vars indices1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24297
                                                      FStar_SMTEncoding_Util.mk_and_l
                                                     in
                                                  let uu____24321 =
                                                    let uu____24322 =
                                                      let uu____24327 =
                                                        let uu____24328 =
                                                          let uu____24333 =
                                                            mk_data_tester
                                                              env1 l xx
                                                             in
                                                          (uu____24333, eqs)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAnd
                                                          uu____24328
                                                         in
                                                      (out, uu____24327)  in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____24322
                                                     in
                                                  (uu____24321,
                                                    (FStar_List.append decls
                                                       decls'))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____24077 with
                    | (data_ax,decls) ->
                        let uu____24346 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____24346 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24357 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24357 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____24361 =
                                 let uu____24368 =
                                   let uu____24369 =
                                     let uu____24380 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____24395 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____24380,
                                       uu____24395)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24369
                                    in
                                 let uu____24410 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____24368,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24410)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____24361
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____24413 =
            let uu____24426 =
              let uu____24427 = FStar_Syntax_Subst.compress k  in
              uu____24427.FStar_Syntax_Syntax.n  in
            match uu____24426 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24472 -> (tps, k)  in
          (match uu____24413 with
           | (formals,res) ->
               let uu____24495 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____24495 with
                | (formals1,res1) ->
                    let uu____24506 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____24506 with
                     | (vars,guards,env',binder_decls,uu____24531) ->
                         let arity = FStar_List.length vars  in
                         let uu____24545 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____24545 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24568 =
                                  let uu____24575 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24575)  in
                                FStar_SMTEncoding_Util.mkApp uu____24568  in
                              let uu____24584 =
                                let tname_decl =
                                  let uu____24594 =
                                    let uu____24595 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24627  ->
                                              match uu____24627 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24640 = varops.next_id ()  in
                                    (tname, uu____24595,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24640, false)
                                     in
                                  constructor_or_logic_type_decl uu____24594
                                   in
                                let uu____24649 =
                                  match vars with
                                  | [] ->
                                      let uu____24662 =
                                        let uu____24663 =
                                          let uu____24666 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____24666
                                           in
                                        push_free_var env1 t arity tname
                                          uu____24663
                                         in
                                      ([], uu____24662)
                                  | uu____24677 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24686 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24686
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24700 =
                                          let uu____24707 =
                                            let uu____24708 =
                                              let uu____24723 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24723)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24708
                                             in
                                          (uu____24707,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24700
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24649 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24584 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24763 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24763 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24781 =
                                               let uu____24782 =
                                                 let uu____24789 =
                                                   let uu____24790 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24790
                                                    in
                                                 (uu____24789,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24782
                                                in
                                             [uu____24781]
                                           else []  in
                                         let uu____24794 =
                                           let uu____24797 =
                                             let uu____24800 =
                                               let uu____24801 =
                                                 let uu____24808 =
                                                   let uu____24809 =
                                                     let uu____24820 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24820)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24809
                                                    in
                                                 (uu____24808,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24801
                                                in
                                             [uu____24800]  in
                                           FStar_List.append karr uu____24797
                                            in
                                         FStar_List.append decls1 uu____24794
                                      in
                                   let aux =
                                     let uu____24836 =
                                       let uu____24839 =
                                         inversion_axioms tapp vars  in
                                       let uu____24842 =
                                         let uu____24845 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24845]  in
                                       FStar_List.append uu____24839
                                         uu____24842
                                        in
                                     FStar_List.append kindingAx uu____24836
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24852,uu____24853,uu____24854,uu____24855,uu____24856)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24864,t,uu____24866,n_tps,uu____24868) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24876 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____24876 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____24916 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____24916 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____24937 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24937 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____24951 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____24951 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____25021 =
                                            mk_term_projector_name d x  in
                                          (uu____25021,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____25023 =
                                  let uu____25042 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____25042, true)
                                   in
                                FStar_All.pipe_right uu____25023
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
                              let uu____25081 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____25081 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____25093::uu____25094 ->
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
                                         let uu____25139 =
                                           let uu____25150 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____25150)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____25139
                                     | uu____25175 -> tok_typing  in
                                   let uu____25184 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____25184 with
                                    | (vars',guards',env'',decls_formals,uu____25209)
                                        ->
                                        let uu____25222 =
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
                                        (match uu____25222 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25253 ->
                                                   let uu____25260 =
                                                     let uu____25261 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25261
                                                      in
                                                   [uu____25260]
                                                in
                                             let encode_elim uu____25272 =
                                               let uu____25273 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____25273 with
                                               | (head1,args) ->
                                                   let uu____25316 =
                                                     let uu____25317 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____25317.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____25316 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25327;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25328;_},uu____25329)
                                                        ->
                                                        let uu____25334 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25334
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25347
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25347
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
                                                                    uu____25393
                                                                    ->
                                                                    let uu____25394
                                                                    =
                                                                    let uu____25399
                                                                    =
                                                                    let uu____25400
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25400
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25399)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25394
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25416
                                                                    =
                                                                    let uu____25417
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25417
                                                                     in
                                                                    if
                                                                    uu____25416
                                                                    then
                                                                    let uu____25430
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25430]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25432
                                                                    =
                                                                    let uu____25445
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____25495
                                                                     ->
                                                                    fun
                                                                    uu____25496
                                                                     ->
                                                                    match 
                                                                    (uu____25495,
                                                                    uu____25496)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25591
                                                                    =
                                                                    let uu____25598
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25598
                                                                     in
                                                                    (match uu____25591
                                                                    with
                                                                    | 
                                                                    (uu____25611,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25619
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25619
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25621
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25621
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
                                                                    uu____25445
                                                                     in
                                                                  (match uu____25432
                                                                   with
                                                                   | 
                                                                   (uu____25636,arg_vars,elim_eqns_or_guards,uu____25639)
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
                                                                    let uu____25667
                                                                    =
                                                                    let uu____25674
                                                                    =
                                                                    let uu____25675
                                                                    =
                                                                    let uu____25686
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25697
                                                                    =
                                                                    let uu____25698
                                                                    =
                                                                    let uu____25703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25703)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25698
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25686,
                                                                    uu____25697)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25675
                                                                     in
                                                                    (uu____25674,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25667
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____25721
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____25721
                                                                    then
                                                                    let x =
                                                                    let uu____25727
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25727,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25729
                                                                    =
                                                                    let uu____25736
                                                                    =
                                                                    let uu____25737
                                                                    =
                                                                    let uu____25748
                                                                    =
                                                                    let uu____25753
                                                                    =
                                                                    let uu____25756
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25756]
                                                                     in
                                                                    [uu____25753]
                                                                     in
                                                                    let uu____25761
                                                                    =
                                                                    let uu____25762
                                                                    =
                                                                    let uu____25767
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25768
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25767,
                                                                    uu____25768)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25762
                                                                     in
                                                                    (uu____25748,
                                                                    [x],
                                                                    uu____25761)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25737
                                                                     in
                                                                    let uu____25787
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25736,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25787)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25729
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25794
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
                                                                    (let uu____25822
                                                                    =
                                                                    let uu____25823
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25823
                                                                    dapp1  in
                                                                    [uu____25822])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25794
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25830
                                                                    =
                                                                    let uu____25837
                                                                    =
                                                                    let uu____25838
                                                                    =
                                                                    let uu____25849
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25860
                                                                    =
                                                                    let uu____25861
                                                                    =
                                                                    let uu____25866
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25866)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25861
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25849,
                                                                    uu____25860)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25838
                                                                     in
                                                                    (uu____25837,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25830)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____25886 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____25886
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____25899
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____25899
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
                                                                    uu____25945
                                                                    ->
                                                                    let uu____25946
                                                                    =
                                                                    let uu____25951
                                                                    =
                                                                    let uu____25952
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25952
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25951)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25946
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25968
                                                                    =
                                                                    let uu____25969
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25969
                                                                     in
                                                                    if
                                                                    uu____25968
                                                                    then
                                                                    let uu____25982
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25982]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____25984
                                                                    =
                                                                    let uu____25997
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____26047
                                                                     ->
                                                                    fun
                                                                    uu____26048
                                                                     ->
                                                                    match 
                                                                    (uu____26047,
                                                                    uu____26048)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____26143
                                                                    =
                                                                    let uu____26150
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____26150
                                                                     in
                                                                    (match uu____26143
                                                                    with
                                                                    | 
                                                                    (uu____26163,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____26171
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____26171
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____26173
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____26173
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
                                                                    uu____25997
                                                                     in
                                                                  (match uu____25984
                                                                   with
                                                                   | 
                                                                   (uu____26188,arg_vars,elim_eqns_or_guards,uu____26191)
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
                                                                    let uu____26219
                                                                    =
                                                                    let uu____26226
                                                                    =
                                                                    let uu____26227
                                                                    =
                                                                    let uu____26238
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26249
                                                                    =
                                                                    let uu____26250
                                                                    =
                                                                    let uu____26255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____26255)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26250
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26238,
                                                                    uu____26249)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26227
                                                                     in
                                                                    (uu____26226,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26219
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____26273
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____26273
                                                                    then
                                                                    let x =
                                                                    let uu____26279
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____26279,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____26281
                                                                    =
                                                                    let uu____26288
                                                                    =
                                                                    let uu____26289
                                                                    =
                                                                    let uu____26300
                                                                    =
                                                                    let uu____26305
                                                                    =
                                                                    let uu____26308
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____26308]
                                                                     in
                                                                    [uu____26305]
                                                                     in
                                                                    let uu____26313
                                                                    =
                                                                    let uu____26314
                                                                    =
                                                                    let uu____26319
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____26320
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____26319,
                                                                    uu____26320)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26314
                                                                     in
                                                                    (uu____26300,
                                                                    [x],
                                                                    uu____26313)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26289
                                                                     in
                                                                    let uu____26339
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____26288,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26339)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26281
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26346
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
                                                                    (let uu____26374
                                                                    =
                                                                    let uu____26375
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26375
                                                                    dapp1  in
                                                                    [uu____26374])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____26346
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____26382
                                                                    =
                                                                    let uu____26389
                                                                    =
                                                                    let uu____26390
                                                                    =
                                                                    let uu____26401
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____26412
                                                                    =
                                                                    let uu____26413
                                                                    =
                                                                    let uu____26418
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____26418)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26413
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26401,
                                                                    uu____26412)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26390
                                                                     in
                                                                    (uu____26389,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26382)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____26437 ->
                                                        let uu____26438 =
                                                          let uu____26439 =
                                                            let uu____26444 =
                                                              let uu____26445
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____26446
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____26445
                                                                uu____26446
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____26444)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26439
                                                           in
                                                        ([], []))
                                                in
                                             let uu____26451 = encode_elim ()
                                                in
                                             (match uu____26451 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26471 =
                                                      let uu____26474 =
                                                        let uu____26477 =
                                                          let uu____26480 =
                                                            let uu____26483 =
                                                              let uu____26484
                                                                =
                                                                let uu____26495
                                                                  =
                                                                  let uu____26498
                                                                    =
                                                                    let uu____26499
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26499
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26498
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26495)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26484
                                                               in
                                                            [uu____26483]  in
                                                          let uu____26504 =
                                                            let uu____26507 =
                                                              let uu____26510
                                                                =
                                                                let uu____26513
                                                                  =
                                                                  let uu____26516
                                                                    =
                                                                    let uu____26519
                                                                    =
                                                                    let uu____26522
                                                                    =
                                                                    let uu____26523
                                                                    =
                                                                    let uu____26530
                                                                    =
                                                                    let uu____26531
                                                                    =
                                                                    let uu____26542
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26542)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26531
                                                                     in
                                                                    (uu____26530,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26523
                                                                     in
                                                                    let uu____26555
                                                                    =
                                                                    let uu____26558
                                                                    =
                                                                    let uu____26559
                                                                    =
                                                                    let uu____26566
                                                                    =
                                                                    let uu____26567
                                                                    =
                                                                    let uu____26578
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____26589
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26578,
                                                                    uu____26589)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26567
                                                                     in
                                                                    (uu____26566,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26559
                                                                     in
                                                                    [uu____26558]
                                                                     in
                                                                    uu____26522
                                                                    ::
                                                                    uu____26555
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26519
                                                                     in
                                                                  FStar_List.append
                                                                    uu____26516
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26513
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26510
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26507
                                                             in
                                                          FStar_List.append
                                                            uu____26480
                                                            uu____26504
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____26477
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____26474
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26471
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
           (fun uu____26635  ->
              fun se  ->
                match uu____26635 with
                | (g,env1) ->
                    let uu____26655 = encode_sigelt env1 se  in
                    (match uu____26655 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26718 =
        match uu____26718 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26750 ->
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
                 let uu____26755 =
                   let uu____26756 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26756
                   then
                     let uu____26757 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26758 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26759 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26757 uu____26758 uu____26759
                   else ()  in
                 let uu____26761 = encode_term t1 env1  in
                 (match uu____26761 with
                  | (t,decls') ->
                      let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                      let uu____26777 =
                        let uu____26784 =
                          let uu____26785 =
                            let uu____26786 =
                              FStar_Util.digest_of_string t_hash  in
                            Prims.strcat uu____26786
                              (Prims.strcat "_" (Prims.string_of_int i))
                             in
                          Prims.strcat "x_" uu____26785  in
                        new_term_constant_from_string env1 x uu____26784  in
                      (match uu____26777 with
                       | (xxsym,xx,env') ->
                           let t2 =
                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                               FStar_Pervasives_Native.None xx t
                              in
                           let caption =
                             let uu____26802 = FStar_Options.log_queries ()
                                in
                             if uu____26802
                             then
                               let uu____26805 =
                                 let uu____26806 =
                                   FStar_Syntax_Print.bv_to_string x  in
                                 let uu____26807 =
                                   FStar_Syntax_Print.term_to_string
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____26808 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 FStar_Util.format3 "%s : %s (%s)"
                                   uu____26806 uu____26807 uu____26808
                                  in
                               FStar_Pervasives_Native.Some uu____26805
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
                                    caption)] (FStar_List.append decls' [ax])
                              in
                           ((i + (Prims.parse_int "1")),
                             (FStar_List.append decls g), env')))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26824,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26838 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26838 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26861,se,uu____26863) ->
                 let uu____26868 = encode_sigelt env1 se  in
                 (match uu____26868 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26885,se) ->
                 let uu____26891 = encode_sigelt env1 se  in
                 (match uu____26891 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26908 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26908 with | (uu____26931,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26946 'Auu____26947 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26946,'Auu____26947)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____27016  ->
              match uu____27016 with
              | (l,uu____27028,uu____27029) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____27075  ->
              match uu____27075 with
              | (l,uu____27089,uu____27090) ->
                  let uu____27099 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____27100 =
                    let uu____27103 =
                      let uu____27104 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____27104  in
                    [uu____27103]  in
                  uu____27099 :: uu____27100))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____27131 =
      let uu____27134 =
        let uu____27135 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____27138 =
          let uu____27139 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____27139 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____27135;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____27138
        }  in
      [uu____27134]  in
    FStar_ST.op_Colon_Equals last_env uu____27131
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____27177 = FStar_ST.op_Bang last_env  in
      match uu____27177 with
      | [] -> failwith "No env; call init first!"
      | e::uu____27208 ->
          let uu___133_27211 = e  in
          let uu____27212 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___133_27211.bindings);
            depth = (uu___133_27211.depth);
            tcenv;
            warn = (uu___133_27211.warn);
            cache = (uu___133_27211.cache);
            nolabels = (uu___133_27211.nolabels);
            use_zfuel_name = (uu___133_27211.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_27211.encode_non_total_function_typ);
            current_module_name = uu____27212
          }
  
let (set_env : env_t -> unit) =
  fun env  ->
    let uu____27218 = FStar_ST.op_Bang last_env  in
    match uu____27218 with
    | [] -> failwith "Empty env stack"
    | uu____27248::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____27283  ->
    let uu____27284 = FStar_ST.op_Bang last_env  in
    match uu____27284 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___134_27322 = hd1  in
          {
            bindings = (uu___134_27322.bindings);
            depth = (uu___134_27322.depth);
            tcenv = (uu___134_27322.tcenv);
            warn = (uu___134_27322.warn);
            cache = refs;
            nolabels = (uu___134_27322.nolabels);
            use_zfuel_name = (uu___134_27322.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_27322.encode_non_total_function_typ);
            current_module_name = (uu___134_27322.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____27354  ->
    let uu____27355 = FStar_ST.op_Bang last_env  in
    match uu____27355 with
    | [] -> failwith "Popping an empty stack"
    | uu____27385::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____27421 = init_env tcenv  in
    let uu____27422 = FStar_SMTEncoding_Z3.init ()  in
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> unit) =
  fun msg  ->
    let uu____27428 = push_env ()  in
    let uu____27429 = varops.push ()  in FStar_SMTEncoding_Z3.push msg
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    let uu____27435 = pop_env ()  in
    let uu____27436 = varops.pop ()  in FStar_SMTEncoding_Z3.pop msg
  
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
        | (uu____27467::uu____27468,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___135_27476 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___135_27476.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___135_27476.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___135_27476.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27477 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____27496 =
        let uu____27499 =
          let uu____27500 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27500  in
        let uu____27501 = open_fact_db_tags env  in uu____27499 ::
          uu____27501
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27496
  
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
      let uu____27527 = encode_sigelt env se  in
      match uu____27527 with
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
        let uu____27568 = FStar_Options.log_queries ()  in
        if uu____27568
        then
          let uu____27571 =
            let uu____27572 =
              let uu____27573 =
                let uu____27574 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27574 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27573  in
            FStar_SMTEncoding_Term.Caption uu____27572  in
          uu____27571 :: decls
        else decls  in
      let uu____27584 =
        let uu____27585 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
           in
        if uu____27585
        then
          let uu____27586 = FStar_Syntax_Print.sigelt_to_string se  in
          FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27586
        else ()  in
      let env =
        let uu____27589 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____27589 tcenv  in
      let uu____27590 = encode_top_level_facts env se  in
      match uu____27590 with
      | (decls,env1) ->
          let uu____27603 = set_env env1  in
          let uu____27604 = caption decls  in
          FStar_SMTEncoding_Z3.giveZ3 uu____27604
  
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
      let uu____27619 =
        let uu____27620 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
           in
        if uu____27620
        then
          let uu____27621 =
            FStar_All.pipe_right
              (FStar_List.length modul.FStar_Syntax_Syntax.exports)
              Prims.string_of_int
             in
          FStar_Util.print2
            "+++++++++++Encoding externals for %s ... %s exports\n" name
            uu____27621
        else ()  in
      let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
      let encode_signature env1 ses =
        FStar_All.pipe_right ses
          (FStar_List.fold_left
             (fun uu____27658  ->
                fun se  ->
                  match uu____27658 with
                  | (g,env2) ->
                      let uu____27678 = encode_top_level_facts env2 se  in
                      (match uu____27678 with
                       | (g',env3) -> ((FStar_List.append g g'), env3)))
             ([], env1))
         in
      let uu____27701 =
        encode_signature
          (let uu___136_27710 = env  in
           {
             bindings = (uu___136_27710.bindings);
             depth = (uu___136_27710.depth);
             tcenv = (uu___136_27710.tcenv);
             warn = false;
             cache = (uu___136_27710.cache);
             nolabels = (uu___136_27710.nolabels);
             use_zfuel_name = (uu___136_27710.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___136_27710.encode_non_total_function_typ);
             current_module_name = (uu___136_27710.current_module_name)
           }) modul.FStar_Syntax_Syntax.exports
         in
      match uu____27701 with
      | (decls,env1) ->
          let caption decls1 =
            let uu____27728 = FStar_Options.log_queries ()  in
            if uu____27728
            then
              let msg = Prims.strcat "Externals for " name  in
              FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                decls1)
                [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
            else decls1  in
          let uu____27733 =
            set_env
              (let uu___137_27736 = env1  in
               {
                 bindings = (uu___137_27736.bindings);
                 depth = (uu___137_27736.depth);
                 tcenv = (uu___137_27736.tcenv);
                 warn = true;
                 cache = (uu___137_27736.cache);
                 nolabels = (uu___137_27736.nolabels);
                 use_zfuel_name = (uu___137_27736.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___137_27736.encode_non_total_function_typ);
                 current_module_name = (uu___137_27736.current_module_name)
               })
             in
          let uu____27737 =
            let uu____27738 =
              FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
            if uu____27738
            then FStar_Util.print1 "Done encoding externals for %s\n" name
            else ()  in
          let decls1 = caption decls  in FStar_SMTEncoding_Z3.giveZ3 decls1
  
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
        let uu____27795 =
          let uu____27796 =
            let uu____27797 = FStar_TypeChecker_Env.current_module tcenv  in
            uu____27797.FStar_Ident.str  in
          FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
            uu____27796
           in
        let env =
          let uu____27799 = FStar_TypeChecker_Env.current_module tcenv  in
          get_env uu____27799 tcenv  in
        let bindings =
          FStar_TypeChecker_Env.fold_env tcenv (fun bs  -> fun b  -> b :: bs)
            []
           in
        let uu____27811 =
          let rec aux bindings1 =
            match bindings1 with
            | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                let uu____27847 = aux rest  in
                (match uu____27847 with
                 | (out,rest1) ->
                     let t =
                       let uu____27877 =
                         FStar_Syntax_Util.destruct_typ_as_formula
                           x.FStar_Syntax_Syntax.sort
                          in
                       match uu____27877 with
                       | FStar_Pervasives_Native.Some uu____27882 ->
                           let uu____27883 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit
                              in
                           FStar_Syntax_Util.refine uu____27883
                             x.FStar_Syntax_Syntax.sort
                       | uu____27884 -> x.FStar_Syntax_Syntax.sort  in
                     let t1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Simplify;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv t
                        in
                     let uu____27888 =
                       let uu____27891 =
                         FStar_Syntax_Syntax.mk_binder
                           (let uu___138_27894 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___138_27894.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___138_27894.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       uu____27891 :: out  in
                     (uu____27888, rest1))
            | uu____27899 -> ([], bindings1)  in
          let uu____27906 = aux bindings  in
          match uu____27906 with
          | (closing,bindings1) ->
              let uu____27931 =
                FStar_Syntax_Util.close_forall_no_univs
                  (FStar_List.rev closing) q
                 in
              (uu____27931, bindings1)
           in
        match uu____27811 with
        | (q1,bindings1) ->
            let uu____27954 =
              let uu____27959 =
                FStar_List.filter
                  (fun uu___103_27964  ->
                     match uu___103_27964 with
                     | FStar_TypeChecker_Env.Binding_sig uu____27965 -> false
                     | uu____27972 -> true) bindings1
                 in
              encode_env_bindings env uu____27959  in
            (match uu____27954 with
             | (env_decls,env1) ->
                 let uu____27989 =
                   let uu____27990 =
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
                   if uu____27990
                   then
                     let uu____27991 = FStar_Syntax_Print.term_to_string q1
                        in
                     FStar_Util.print1 "Encoding query formula: %s\n"
                       uu____27991
                   else ()  in
                 let uu____27993 = encode_formula q1 env1  in
                 (match uu____27993 with
                  | (phi,qdecls) ->
                      let uu____28014 =
                        let uu____28019 =
                          FStar_TypeChecker_Env.get_range tcenv  in
                        FStar_SMTEncoding_ErrorReporting.label_goals
                          use_env_msg uu____28019 phi
                         in
                      (match uu____28014 with
                       | (labels,phi1) ->
                           let uu____28036 = encode_labels labels  in
                           (match uu____28036 with
                            | (label_prefix,label_suffix) ->
                                let query_prelude =
                                  FStar_List.append env_decls
                                    (FStar_List.append label_prefix qdecls)
                                   in
                                let qry =
                                  let uu____28073 =
                                    let uu____28080 =
                                      FStar_SMTEncoding_Util.mkNot phi1  in
                                    let uu____28081 =
                                      varops.mk_unique "@query"  in
                                    (uu____28080,
                                      (FStar_Pervasives_Native.Some "query"),
                                      uu____28081)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____28073
                                   in
                                let suffix =
                                  FStar_List.append
                                    [FStar_SMTEncoding_Term.Echo "<labels>"]
                                    (FStar_List.append label_suffix
                                       [FStar_SMTEncoding_Term.Echo
                                          "</labels>";
                                       FStar_SMTEncoding_Term.Echo "Done!"])
                                   in
                                (query_prelude, labels, qry, suffix)))))
  