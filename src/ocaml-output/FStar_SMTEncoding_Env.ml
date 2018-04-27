open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____4 -> false
  
let add_fuel :
  'Auu____8 . 'Auu____8 -> 'Auu____8 Prims.list -> 'Auu____8 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____23 = FStar_Options.unthrottle_inductives ()  in
      if uu____23 then tl1 else x :: tl1
  
let withenv :
  'Auu____32 'Auu____33 'Auu____34 .
    'Auu____32 ->
      ('Auu____33,'Auu____34) FStar_Pervasives_Native.tuple2 ->
        ('Auu____33,'Auu____34,'Auu____32) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____52  -> match uu____52 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____63 'Auu____64 'Auu____65 .
    (('Auu____63,'Auu____64) FStar_Util.either,'Auu____65)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____63,'Auu____64) FStar_Util.either,'Auu____65)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___55_111  ->
         match uu___55_111 with
         | (FStar_Util.Inl uu____120,uu____121) -> false
         | uu____126 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___57_147 = a  in
        let uu____148 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____148;
          FStar_Syntax_Syntax.index = (uu___57_147.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___57_147.FStar_Syntax_Syntax.sort)
        }  in
      let uu____149 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____149
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____162 =
          let uu____163 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____163  in
        let uu____164 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____164 with
        | (uu____169,t) ->
            let uu____171 =
              let uu____172 = FStar_Syntax_Subst.compress t  in
              uu____172.FStar_Syntax_Syntax.n  in
            (match uu____171 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____193 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____193 with
                  | (binders,uu____199) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____214 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____221 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____221
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____228 =
        let uu____233 = mk_term_projector_name lid a  in
        (uu____233,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____228
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____240 =
        let uu____245 = mk_term_projector_name_by_pos lid i  in
        (uu____245,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____240
  
let mk_data_tester :
  'Auu____250 .
    'Auu____250 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
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
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit) =
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
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int)
  =
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
  let new_scope uu____614 =
    let uu____615 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____618 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____615, uu____618)  in
  let scopes =
    let uu____638 = let uu____649 = new_scope ()  in [uu____649]  in
    FStar_Util.mk_ref uu____638  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____690 =
        let uu____693 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____693
          (fun uu____776  ->
             match uu____776 with
             | (names1,uu____788) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____690 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____797 ->
          (FStar_Util.incr ctr;
           (let uu____832 =
              let uu____833 =
                let uu____834 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____834  in
              Prims.strcat "__" uu____833  in
            Prims.strcat y1 uu____832))
       in
    let top_scope =
      let uu____879 =
        let uu____888 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____888
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____879  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____997 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1077 =
      let uu____1078 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1078  in
    FStar_Util.format2 "%s_%s" pfx uu____1077  in
  let string_const s =
    let uu____1083 =
      let uu____1086 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1086
        (fun uu____1169  ->
           match uu____1169 with
           | (uu____1180,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1083 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1193 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1193  in
        let top_scope =
          let uu____1197 =
            let uu____1206 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1206  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1197  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1304 =
    let uu____1305 =
      let uu____1316 = new_scope ()  in
      let uu____1325 = FStar_ST.op_Bang scopes  in uu____1316 :: uu____1325
       in
    FStar_ST.op_Colon_Equals scopes uu____1305  in
  let pop1 uu____1469 =
    let uu____1470 =
      let uu____1481 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1481
       in
    FStar_ST.op_Colon_Equals scopes uu____1470  in
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
    let uu___58_1625 = x  in
    let uu____1626 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1626;
      FStar_Syntax_Syntax.index = (uu___58_1625.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___58_1625.FStar_Syntax_Syntax.sort)
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
  
let binder_of_eithervar :
  'Auu____1722 'Auu____1723 .
    'Auu____1722 ->
      ('Auu____1722,'Auu____1723 FStar_Pervasives_Native.option)
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
  encoding_quantifier: Prims.bool }[@@deriving show]
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
  'Auu____2193 .
    'Auu____2193 ->
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
                 (fun uu___56_2227  ->
                    match uu___56_2227 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2231 -> []))
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
                    fun uu____2278  ->
                      fun acc1  ->
                        match uu____2278 with
                        | (x,_term) ->
                            let uu____2290 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____2290 :: acc1) acc) []
       in
    let allvars =
      FStar_Util.psmap_fold e.fvar_bindings
        (fun _k  ->
           fun fvb  ->
             fun acc  ->
               let uu____2305 = FStar_Syntax_Print.lid_to_string fvb.fvar_lid
                  in
               uu____2305 :: acc) bvars
       in
    FStar_String.concat ", " allvars
  
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      let uu____2318 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____2318 with
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
  'Auu____2377 .
    (FStar_Syntax_Syntax.bv,'Auu____2377) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____2377) FStar_Pervasives_Native.tuple2
        FStar_Util.pimap FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv,'Auu____2377) FStar_Pervasives_Native.tuple2
          FStar_Util.pimap FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____2435 =
             let uu____2442 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____2442 pimap_opt  in
           FStar_Util.pimap_add uu____2435
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
      let uu____2486 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2486)
  
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
      let uu____2501 =
        let uu___59_2502 = env  in
        let uu____2503 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____2503;
          fvar_bindings = (uu___59_2502.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___59_2502.tcenv);
          warn = (uu___59_2502.warn);
          cache = (uu___59_2502.cache);
          nolabels = (uu___59_2502.nolabels);
          use_zfuel_name = (uu___59_2502.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___59_2502.encode_non_total_function_typ);
          current_module_name = (uu___59_2502.current_module_name);
          encoding_quantifier = (uu___59_2502.encoding_quantifier)
        }  in
      (ysym, y, uu____2501)
  
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
      let uu____2528 =
        let uu___60_2529 = env  in
        let uu____2530 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____2530;
          fvar_bindings = (uu___60_2529.fvar_bindings);
          depth = (uu___60_2529.depth);
          tcenv = (uu___60_2529.tcenv);
          warn = (uu___60_2529.warn);
          cache = (uu___60_2529.cache);
          nolabels = (uu___60_2529.nolabels);
          use_zfuel_name = (uu___60_2529.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___60_2529.encode_non_total_function_typ);
          current_module_name = (uu___60_2529.current_module_name);
          encoding_quantifier = (uu___60_2529.encoding_quantifier)
        }  in
      (ysym, y, uu____2528)
  
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
        let uu____2558 =
          let uu___61_2559 = env  in
          let uu____2560 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____2560;
            fvar_bindings = (uu___61_2559.fvar_bindings);
            depth = (uu___61_2559.depth);
            tcenv = (uu___61_2559.tcenv);
            warn = (uu___61_2559.warn);
            cache = (uu___61_2559.cache);
            nolabels = (uu___61_2559.nolabels);
            use_zfuel_name = (uu___61_2559.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___61_2559.encode_non_total_function_typ);
            current_module_name = (uu___61_2559.current_module_name);
            encoding_quantifier = (uu___61_2559.encoding_quantifier)
          }  in
        (ysym, y, uu____2558)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___62_2578 = env  in
        let uu____2579 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____2579;
          fvar_bindings = (uu___62_2578.fvar_bindings);
          depth = (uu___62_2578.depth);
          tcenv = (uu___62_2578.tcenv);
          warn = (uu___62_2578.warn);
          cache = (uu___62_2578.cache);
          nolabels = (uu___62_2578.nolabels);
          use_zfuel_name = (uu___62_2578.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___62_2578.encode_non_total_function_typ);
          current_module_name = (uu___62_2578.current_module_name);
          encoding_quantifier = (uu___62_2578.encoding_quantifier)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____2594 = lookup_bvar_binding env a  in
      match uu____2594 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2606 = lookup_bvar_binding env a2  in
          (match uu____2606 with
           | FStar_Pervasives_Native.None  ->
               let uu____2617 =
                 let uu____2618 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2619 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2618 uu____2619
                  in
               failwith uu____2617
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
        let uu____2676 =
          let uu___63_2677 = env  in
          let uu____2678 = add_fvar_binding fvb env.fvar_bindings  in
          {
            bvar_bindings = (uu___63_2677.bvar_bindings);
            fvar_bindings = uu____2678;
            depth = (uu___63_2677.depth);
            tcenv = (uu___63_2677.tcenv);
            warn = (uu___63_2677.warn);
            cache = (uu___63_2677.cache);
            nolabels = (uu___63_2677.nolabels);
            use_zfuel_name = (uu___63_2677.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___63_2677.encode_non_total_function_typ);
            current_module_name = (uu___63_2677.current_module_name);
            encoding_quantifier = (uu___63_2677.encoding_quantifier)
          }  in
        (fname, ftok_name, uu____2676)
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2687 = lookup_fvar_binding env a  in
      match uu____2687 with
      | FStar_Pervasives_Native.None  ->
          let uu____2690 =
            let uu____2691 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2691  in
          failwith uu____2690
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
            let uu___64_2713 = env  in
            let uu____2714 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___64_2713.bvar_bindings);
              fvar_bindings = uu____2714;
              depth = (uu___64_2713.depth);
              tcenv = (uu___64_2713.tcenv);
              warn = (uu___64_2713.warn);
              cache = (uu___64_2713.cache);
              nolabels = (uu___64_2713.nolabels);
              use_zfuel_name = (uu___64_2713.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___64_2713.encode_non_total_function_typ);
              current_module_name = (uu___64_2713.current_module_name);
              encoding_quantifier = (uu___64_2713.encoding_quantifier)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2728 =
            let uu____2735 =
              let uu____2738 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2738]  in
            (f, uu____2735)  in
          FStar_SMTEncoding_Util.mkApp uu____2728  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___65_2744 = env  in
        let uu____2745 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___65_2744.bvar_bindings);
          fvar_bindings = uu____2745;
          depth = (uu___65_2744.depth);
          tcenv = (uu___65_2744.tcenv);
          warn = (uu___65_2744.warn);
          cache = (uu___65_2744.cache);
          nolabels = (uu___65_2744.nolabels);
          use_zfuel_name = (uu___65_2744.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___65_2744.encode_non_total_function_typ);
          current_module_name = (uu___65_2744.current_module_name);
          encoding_quantifier = (uu___65_2744.encoding_quantifier)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2756 = lookup_fvar_binding env l  in
      match uu____2756 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2765 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2773,fuel::[]) ->
                         let uu____2777 =
                           let uu____2778 =
                             let uu____2779 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2779
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2778 "fuel"  in
                         if uu____2777
                         then
                           let uu____2782 =
                             let uu____2783 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2783
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
                             uu____2782
                         else FStar_Pervasives_Native.Some t
                     | uu____2787 -> FStar_Pervasives_Native.Some t)
                | uu____2788 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2801 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2801 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2805 =
            let uu____2806 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2806  in
          failwith uu____2805
  
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
            FStar_SMTEncoding_Term.freevars = uu____2851;
            FStar_SMTEncoding_Term.rng = uu____2852;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____2867 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____2895 ->
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
        (fun uu____2908  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  