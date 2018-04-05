open Prims
let add_fuel :
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives ()  in
      if uu____19 then tl1 else x :: tl1
  
let withenv :
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____28 ->
      ('Auu____29,'Auu____30) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____30,'Auu____28) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____59,'Auu____60) FStar_Util.either,'Auu____61)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____59,'Auu____60) FStar_Util.either,'Auu____61)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___81_107  ->
         match uu___81_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___104_143 = a  in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___104_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___104_143.FStar_Syntax_Syntax.sort)
        }  in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____145
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____159  in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____160 with
        | (uu____165,t) ->
            let uu____167 =
              let uu____168 = FStar_Syntax_Subst.compress t  in
              uu____168.FStar_Syntax_Syntax.n  in
            (match uu____167 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____189 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____189 with
                  | (binders,uu____195) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____217
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____224 =
        let uu____229 = mk_term_projector_name lid a  in
        (uu____229,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____224
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____236 =
        let uu____241 = mk_term_projector_name_by_pos lid i  in
        (uu____241,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____236
  
let mk_data_tester :
  'Auu____246 .
    'Auu____246 ->
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
  let new_scope uu____610 =
    let uu____611 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____614 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____611, uu____614)  in
  let scopes =
    let uu____634 = let uu____645 = new_scope ()  in [uu____645]  in
    FStar_Util.mk_ref uu____634  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____686 =
        let uu____689 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____689
          (fun uu____772  ->
             match uu____772 with
             | (names1,uu____784) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____686 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____793 ->
          (FStar_Util.incr ctr;
           (let uu____828 =
              let uu____829 =
                let uu____830 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____830  in
              Prims.strcat "__" uu____829  in
            Prims.strcat y1 uu____828))
       in
    let top_scope =
      let uu____875 =
        let uu____884 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____884
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____875  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____993 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1073 =
      let uu____1074 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1074  in
    FStar_Util.format2 "%s_%s" pfx uu____1073  in
  let string_const s =
    let uu____1079 =
      let uu____1082 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1082
        (fun uu____1165  ->
           match uu____1165 with
           | (uu____1176,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1079 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1189 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1189  in
        let top_scope =
          let uu____1193 =
            let uu____1202 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1202  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1193  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1300 =
    let uu____1301 =
      let uu____1312 = new_scope ()  in
      let uu____1321 = FStar_ST.op_Bang scopes  in uu____1312 :: uu____1321
       in
    FStar_ST.op_Colon_Equals scopes uu____1301  in
  let pop1 uu____1465 =
    let uu____1466 =
      let uu____1477 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1477
       in
    FStar_ST.op_Colon_Equals scopes uu____1466  in
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
    let uu___105_1621 = x  in
    let uu____1622 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1622;
      FStar_Syntax_Syntax.index = (uu___105_1621.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___105_1621.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1735 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1759 -> false
  
let (__proj__Binding_fvar__item___0 : binding -> fvar_binding) =
  fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____1770 'Auu____1771 .
    'Auu____1770 ->
      ('Auu____1770,'Auu____1771 FStar_Pervasives_Native.option)
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
  'Auu____2067 .
    'Auu____2067 ->
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
                 (fun uu___82_2101  ->
                    match uu___82_2101 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2105 -> []))
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
    let uu____2114 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___83_2124  ->
              match uu___83_2124 with
              | Binding_var (x,uu____2126) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid))
       in
    FStar_All.pipe_right uu____2114 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2133 .
    env_t ->
      (binding -> 'Auu____2133 FStar_Pervasives_Native.option) ->
        'Auu____2133 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2161 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2161
      then
        let uu____2164 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2164
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
      let uu____2177 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2177)
  
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
        (let uu___106_2193 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___106_2193.tcenv);
           warn = (uu___106_2193.warn);
           cache = (uu___106_2193.cache);
           nolabels = (uu___106_2193.nolabels);
           use_zfuel_name = (uu___106_2193.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___106_2193.encode_non_total_function_typ);
           current_module_name = (uu___106_2193.current_module_name)
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
        (let uu___107_2211 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___107_2211.depth);
           tcenv = (uu___107_2211.tcenv);
           warn = (uu___107_2211.warn);
           cache = (uu___107_2211.cache);
           nolabels = (uu___107_2211.nolabels);
           use_zfuel_name = (uu___107_2211.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___107_2211.encode_non_total_function_typ);
           current_module_name = (uu___107_2211.current_module_name)
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
          (let uu___108_2232 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___108_2232.depth);
             tcenv = (uu___108_2232.tcenv);
             warn = (uu___108_2232.warn);
             cache = (uu___108_2232.cache);
             nolabels = (uu___108_2232.nolabels);
             use_zfuel_name = (uu___108_2232.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___108_2232.encode_non_total_function_typ);
             current_module_name = (uu___108_2232.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___109_2242 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___109_2242.depth);
          tcenv = (uu___109_2242.tcenv);
          warn = (uu___109_2242.warn);
          cache = (uu___109_2242.cache);
          nolabels = (uu___109_2242.nolabels);
          use_zfuel_name = (uu___109_2242.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___109_2242.encode_non_total_function_typ);
          current_module_name = (uu___109_2242.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___84_2266  ->
             match uu___84_2266 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2279 -> FStar_Pervasives_Native.None)
         in
      let uu____2284 = aux a  in
      match uu____2284 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2296 = aux a2  in
          (match uu____2296 with
           | FStar_Pervasives_Native.None  ->
               let uu____2307 =
                 let uu____2308 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2309 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2308 uu____2309
                  in
               failwith uu____2307
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
          (let uu___110_2367 = env  in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___110_2367.depth);
             tcenv = (uu___110_2367.tcenv);
             warn = (uu___110_2367.warn);
             cache = (uu___110_2367.cache);
             nolabels = (uu___110_2367.nolabels);
             use_zfuel_name = (uu___110_2367.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___110_2367.encode_non_total_function_typ);
             current_module_name = (uu___110_2367.current_module_name)
           }))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___85_2378  ->
           match uu___85_2378 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2382 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2389 =
        lookup_binding env
          (fun uu___86_2394  ->
             match uu___86_2394 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2398 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2389 FStar_Option.isSome
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2407 = try_lookup_lid env a  in
      match uu____2407 with
      | FStar_Pervasives_Native.None  ->
          let uu____2410 =
            let uu____2411 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2411  in
          failwith uu____2410
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
            let uu___111_2433 = env  in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___111_2433.depth);
              tcenv = (uu___111_2433.tcenv);
              warn = (uu___111_2433.warn);
              cache = (uu___111_2433.cache);
              nolabels = (uu___111_2433.nolabels);
              use_zfuel_name = (uu___111_2433.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___111_2433.encode_non_total_function_typ);
              current_module_name = (uu___111_2433.current_module_name)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2445 =
            let uu____2452 =
              let uu____2455 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2455]  in
            (f, uu____2452)  in
          FStar_SMTEncoding_Util.mkApp uu____2445  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___112_2461 = env  in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___112_2461.depth);
          tcenv = (uu___112_2461.tcenv);
          warn = (uu___112_2461.warn);
          cache = (uu___112_2461.cache);
          nolabels = (uu___112_2461.nolabels);
          use_zfuel_name = (uu___112_2461.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___112_2461.encode_non_total_function_typ);
          current_module_name = (uu___112_2461.current_module_name)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2470 = try_lookup_lid env l  in
      match uu____2470 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2479 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2487,fuel::[]) ->
                         let uu____2491 =
                           let uu____2492 =
                             let uu____2493 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2493
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2492 "fuel"  in
                         if uu____2491
                         then
                           let uu____2496 =
                             let uu____2497 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2497
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
                             uu____2496
                         else FStar_Pervasives_Native.Some t
                     | uu____2501 -> FStar_Pervasives_Native.Some t)
                | uu____2502 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2515 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2515 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2519 =
            let uu____2520 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2520  in
          failwith uu____2519
  
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
            FStar_SMTEncoding_Term.freevars = uu____2565;
            FStar_SMTEncoding_Term.rng = uu____2566;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____2581 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____2609 ->
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
        (fun uu___87_2622  ->
           match uu___87_2622 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____2626 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____2630 .
    'Auu____2630 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____2648  ->
      match uu____2648 with
      | (pats,vars,body) ->
          let fallback uu____2673 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____2678 = FStar_Options.unthrottle_inductives ()  in
          if uu____2678
          then fallback ()
          else
            (let uu____2680 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____2680 with
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
                           | uu____2711 -> p))
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
                             let uu____2732 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____2732
                         | uu____2735 ->
                             let uu____2736 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____2736 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____2741 -> body  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____2782 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2795 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2802 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2803 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2820 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2837 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2839 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2839 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2857;
             FStar_Syntax_Syntax.vars = uu____2858;_},uu____2859)
          ->
          let uu____2880 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2880 FStar_Option.isNone
      | uu____2897 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____2904 =
        let uu____2905 = FStar_Syntax_Util.un_uinst t  in
        uu____2905.FStar_Syntax_Syntax.n  in
      match uu____2904 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2908,uu____2909,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___88_2930  ->
                  match uu___88_2930 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2931 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2933 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2933 FStar_Option.isSome
      | uu____2950 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____2957 = head_normal env t  in
      if uu____2957
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
    let uu____2968 =
      let uu____2969 = FStar_Syntax_Syntax.null_binder t  in [uu____2969]  in
    let uu____2970 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____2968 uu____2970 FStar_Pervasives_Native.None
  
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
                    let uu____3008 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3008
                | s ->
                    let uu____3013 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3013) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'Auu____3031 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3031
  =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____3048 =
            let uu____3053 =
              let uu____3054 = FStar_Util.string_of_int arity  in
              let uu____3055 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3054 uu____3055
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3053)  in
          FStar_Errors.raise_error uu____3048 rng
  
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
              (let uu____3086 = FStar_Util.first_N arity args  in
               match uu____3086 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3109 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3109 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___89_3116  ->
    match uu___89_3116 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3117 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____3153;
                       FStar_SMTEncoding_Term.rng = uu____3154;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3177) ->
              let uu____3186 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3197 -> false) args (FStar_List.rev xs))
                 in
              if uu____3186
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3201,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3205 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3209 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3209))
                 in
              if uu____3205
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3213 -> FStar_Pervasives_Native.None  in
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
    Prims.unit ->
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
    Prims.unit ->
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
    | uu____3435 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3439 -> false
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3458 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3471 ->
            let uu____3478 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3478
        | uu____3479 ->
            if norm1
            then let uu____3480 = whnf env t1  in aux false uu____3480
            else
              (let uu____3482 =
                 let uu____3483 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3484 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3483 uu____3484
                  in
               failwith uu____3482)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3516) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3521 ->
        let uu____3522 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3522)
  
let is_arithmetic_primitive :
  'Auu____3536 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3536 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3556::uu____3557::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3561::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3564 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3585 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3600 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____3604 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3604)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____3643)::uu____3644::uu____3645::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3696)::uu____3697::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____3734 -> false
  
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
          let uu____3953 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____3953, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____3956 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____3956, [])
      | FStar_Const.Const_char c1 ->
          let uu____3960 =
            let uu____3961 =
              let uu____3968 =
                let uu____3971 =
                  let uu____3972 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____3972  in
                [uu____3971]  in
              ("FStar.Char.__char_of_int", uu____3968)  in
            FStar_SMTEncoding_Util.mkApp uu____3961  in
          (uu____3960, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____3988 =
            let uu____3989 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____3989  in
          (uu____3988, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4010) ->
          let uu____4011 = varops.string_const s  in (uu____4011, [])
      | FStar_Const.Const_range uu____4014 ->
          let uu____4015 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4015, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4021 =
            let uu____4022 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4022  in
          failwith uu____4021

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
        (let uu____4051 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4051
         then
           let uu____4052 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4052
         else ());
        (let uu____4054 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4138  ->
                   fun b  ->
                     match uu____4138 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4217 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4233 = gen_term_var env1 x  in
                           match uu____4233 with
                           | (xxsym,xx,env') ->
                               let uu____4257 =
                                 let uu____4262 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4262 env1 xx
                                  in
                               (match uu____4257 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4217 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4054 with
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
          let uu____4421 = encode_term t env  in
          match uu____4421 with
          | (t1,decls) ->
              let uu____4432 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____4432, decls)

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
          let uu____4443 = encode_term t env  in
          match uu____4443 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4458 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____4458, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4460 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____4460, decls))

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
        let uu____4466 = encode_args args_e env  in
        match uu____4466 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4485 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____4494 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____4494  in
            let binary arg_tms1 =
              let uu____4507 =
                let uu____4508 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____4508  in
              let uu____4509 =
                let uu____4510 =
                  let uu____4511 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____4511  in
                FStar_SMTEncoding_Term.unboxInt uu____4510  in
              (uu____4507, uu____4509)  in
            let mk_default uu____4517 =
              let uu____4518 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4518 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l a op mk_args ts =
              let uu____4568 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____4568
              then
                let uu____4569 =
                  let uu____4570 = mk_args ts  in op uu____4570  in
                FStar_All.pipe_right uu____4569 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____4599 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____4599
              then
                let uu____4600 = binary ts  in
                match uu____4600 with
                | (t1,t2) ->
                    let uu____4607 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____4607
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4611 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____4611
                 then
                   let uu____4612 = op (binary ts)  in
                   FStar_All.pipe_right uu____4612
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 =
              mk_l ()
                (fun a393  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a393)
                (fun a394  -> (Obj.magic binary) a394)
               in
            let sub1 =
              mk_l ()
                (fun a395  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a395)
                (fun a396  -> (Obj.magic binary) a396)
               in
            let minus =
              mk_l ()
                (fun a397  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a397)
                (fun a398  -> (Obj.magic unary) a398)
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
            let uu____4735 =
              let uu____4744 =
                FStar_List.tryFind
                  (fun uu____4766  ->
                     match uu____4766 with
                     | (l,uu____4776) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____4744 FStar_Util.must  in
            (match uu____4735 with
             | (uu____4815,op) ->
                 let uu____4825 = op arg_tms  in (uu____4825, decls))

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
        let uu____4833 = FStar_List.hd args_e  in
        match uu____4833 with
        | (tm_sz,uu____4841) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____4851 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____4851 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____4859 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____4859);
                   t_decls1)
               in
            let uu____4860 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____4880::(sz_arg,uu____4882)::uu____4883::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____4932 =
                    let uu____4935 = FStar_List.tail args_e  in
                    FStar_List.tail uu____4935  in
                  let uu____4938 =
                    let uu____4941 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____4941  in
                  (uu____4932, uu____4938)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____4947::(sz_arg,uu____4949)::uu____4950::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____4999 =
                    let uu____5000 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5000
                     in
                  failwith uu____4999
              | uu____5009 ->
                  let uu____5016 = FStar_List.tail args_e  in
                  (uu____5016, FStar_Pervasives_Native.None)
               in
            (match uu____4860 with
             | (arg_tms,ext_sz) ->
                 let uu____5039 = encode_args arg_tms env  in
                 (match uu____5039 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5060 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5069 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5069  in
                      let unary_arith arg_tms2 =
                        let uu____5078 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5078  in
                      let binary arg_tms2 =
                        let uu____5091 =
                          let uu____5092 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5092
                           in
                        let uu____5093 =
                          let uu____5094 =
                            let uu____5095 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5095  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5094
                           in
                        (uu____5091, uu____5093)  in
                      let binary_arith arg_tms2 =
                        let uu____5110 =
                          let uu____5111 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5111
                           in
                        let uu____5112 =
                          let uu____5113 =
                            let uu____5114 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5114  in
                          FStar_SMTEncoding_Term.unboxInt uu____5113  in
                        (uu____5110, uu____5112)  in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5156 =
                          let uu____5157 = mk_args ts  in op uu____5157  in
                        FStar_All.pipe_right uu____5156 resBox  in
                      let bv_and =
                        mk_bv ()
                          (fun a399  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a399)
                          (fun a400  -> (Obj.magic binary) a400)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv ()
                          (fun a401  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a401)
                          (fun a402  -> (Obj.magic binary) a402)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv ()
                          (fun a403  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a403)
                          (fun a404  -> (Obj.magic binary) a404)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv ()
                          (fun a405  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a405)
                          (fun a406  -> (Obj.magic binary) a406)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv ()
                          (fun a407  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a407)
                          (fun a408  -> (Obj.magic binary) a408)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv ()
                          (fun a409  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a409)
                          (fun a410  -> (Obj.magic binary_arith) a410)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv ()
                          (fun a411  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a411)
                          (fun a412  -> (Obj.magic binary_arith) a412)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv ()
                          (fun a413  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a413)
                          (fun a414  -> (Obj.magic binary_arith) a414)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv ()
                          (fun a415  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a415)
                          (fun a416  -> (Obj.magic binary_arith) a416)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv ()
                          (fun a417  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a417)
                          (fun a418  -> (Obj.magic binary_arith) a418)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv ()
                          (fun a419  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a419)
                          (fun a420  -> (Obj.magic binary) a420)
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____5221 =
                          let uu____5224 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5224  in
                        let uu____5226 =
                          let uu____5229 =
                            let uu____5230 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5230  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5229  in
                        mk_bv () (fun a421  -> (Obj.magic uu____5221) a421)
                          (fun a422  -> (Obj.magic unary) a422) uu____5226
                          arg_tms2
                         in
                      let to_int1 =
                        mk_bv ()
                          (fun a423  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a423) (fun a424  -> (Obj.magic unary) a424)
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv ()
                          (fun a425  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a425)
                          (fun a426  -> (Obj.magic unary_arith) a426)
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
                      let uu____5429 =
                        let uu____5438 =
                          FStar_List.tryFind
                            (fun uu____5460  ->
                               match uu____5460 with
                               | (l,uu____5470) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____5438 FStar_Util.must  in
                      (match uu____5429 with
                       | (uu____5511,op) ->
                           let uu____5521 = op arg_tms1  in
                           (uu____5521, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____5532 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____5532
       then
         let uu____5533 = FStar_Syntax_Print.tag_of_term t  in
         let uu____5534 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____5535 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5533 uu____5534
           uu____5535
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5541 ->
           let uu____5566 =
             let uu____5567 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5568 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5569 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5570 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5567
               uu____5568 uu____5569 uu____5570
              in
           failwith uu____5566
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5575 =
             let uu____5576 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5577 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5578 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5579 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5576
               uu____5577 uu____5578 uu____5579
              in
           failwith uu____5575
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5585 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____5585 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5587 =
             let uu____5588 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5588
              in
           failwith uu____5587
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____5595),uu____5596) ->
           let uu____5645 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____5653 -> false  in
           if uu____5645
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____5670) ->
           let tv =
             let uu____5676 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____5676
              in
           let t1 =
             let uu____5680 =
               let uu____5689 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____5689]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____5680
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5691) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5701 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____5701, [])
       | FStar_Syntax_Syntax.Tm_type uu____5704 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5708) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____5733 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5733 with
            | (binders1,res) ->
                let uu____5744 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5744
                then
                  let uu____5749 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5749 with
                   | (vars,guards,env',decls,uu____5774) ->
                       let fsym =
                         let uu____5792 = varops.fresh "f"  in
                         (uu____5792, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5795 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___113_5804 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___113_5804.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___113_5804.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___113_5804.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___113_5804.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___113_5804.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___113_5804.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___113_5804.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___113_5804.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___113_5804.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___113_5804.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___113_5804.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___113_5804.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___113_5804.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___113_5804.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___113_5804.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___113_5804.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___113_5804.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___113_5804.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___113_5804.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___113_5804.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___113_5804.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___113_5804.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___113_5804.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___113_5804.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___113_5804.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___113_5804.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___113_5804.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___113_5804.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___113_5804.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___113_5804.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___113_5804.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___113_5804.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___113_5804.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___113_5804.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___113_5804.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___113_5804.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____5795 with
                        | (pre_opt,res_t) ->
                            let uu____5815 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5815 with
                             | (res_pred,decls') ->
                                 let uu____5826 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5839 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____5839, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5843 =
                                         encode_formula pre env'  in
                                       (match uu____5843 with
                                        | (guard,decls0) ->
                                            let uu____5856 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____5856, decls0))
                                    in
                                 (match uu____5826 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____5868 =
                                          let uu____5879 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____5879)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5868
                                         in
                                      let cvars =
                                        let uu____5897 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____5897
                                          (FStar_List.filter
                                             (fun uu____5911  ->
                                                match uu____5911 with
                                                | (x,uu____5917) ->
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
                                      let uu____5936 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____5936 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5944 =
                                             let uu____5945 =
                                               let uu____5952 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5952)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5945
                                              in
                                           (uu____5944,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____5972 =
                                               let uu____5973 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____5973
                                                in
                                             varops.mk_unique uu____5972  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____5984 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____5984
                                             then
                                               let uu____5987 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____5987
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
                                             let uu____5995 =
                                               let uu____6002 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6002)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5995
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
                                             let uu____6014 =
                                               let uu____6021 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6021,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6014
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
                                             let uu____6042 =
                                               let uu____6049 =
                                                 let uu____6050 =
                                                   let uu____6061 =
                                                     let uu____6062 =
                                                       let uu____6067 =
                                                         let uu____6068 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6068
                                                          in
                                                       (f_has_t, uu____6067)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6062
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6061)
                                                    in
                                                 mkForall_fuel uu____6050  in
                                               (uu____6049,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6042
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6091 =
                                               let uu____6098 =
                                                 let uu____6099 =
                                                   let uu____6110 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6110)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6099
                                                  in
                                               (uu____6098,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6091
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
                                           ((let uu____6135 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6135);
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
                     let uu____6150 =
                       let uu____6157 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6157,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6150  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6169 =
                       let uu____6176 =
                         let uu____6177 =
                           let uu____6188 =
                             let uu____6189 =
                               let uu____6194 =
                                 let uu____6195 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6195
                                  in
                               (f_has_t, uu____6194)  in
                             FStar_SMTEncoding_Util.mkImp uu____6189  in
                           ([[f_has_t]], [fsym], uu____6188)  in
                         mkForall_fuel uu____6177  in
                       (uu____6176, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6169  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6222 ->
           let uu____6229 =
             let uu____6234 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6234 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6241;
                 FStar_Syntax_Syntax.vars = uu____6242;_} ->
                 let uu____6249 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6249 with
                  | (b,f1) ->
                      let uu____6274 =
                        let uu____6275 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6275  in
                      (uu____6274, f1))
             | uu____6284 -> failwith "impossible"  in
           (match uu____6229 with
            | (x,f) ->
                let uu____6295 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6295 with
                 | (base_t,decls) ->
                     let uu____6306 = gen_term_var env x  in
                     (match uu____6306 with
                      | (x1,xtm,env') ->
                          let uu____6320 = encode_formula f env'  in
                          (match uu____6320 with
                           | (refinement,decls') ->
                               let uu____6331 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6331 with
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
                                      let uu____6347 =
                                        let uu____6350 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6357 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6350
                                          uu____6357
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6347
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6390  ->
                                              match uu____6390 with
                                              | (y,uu____6396) ->
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
                                    let uu____6429 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6429 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6437 =
                                           let uu____6438 =
                                             let uu____6445 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6445)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6438
                                            in
                                         (uu____6437,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6466 =
                                             let uu____6467 =
                                               let uu____6468 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6468
                                                in
                                             Prims.strcat module_name
                                               uu____6467
                                              in
                                           varops.mk_unique uu____6466  in
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
                                           let uu____6482 =
                                             let uu____6489 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6489)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6482
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
                                           let uu____6504 =
                                             let uu____6511 =
                                               let uu____6512 =
                                                 let uu____6523 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6523)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6512
                                                in
                                             (uu____6511,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6504
                                            in
                                         let t_kinding =
                                           let uu____6541 =
                                             let uu____6548 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6548,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6541
                                            in
                                         let t_interp =
                                           let uu____6566 =
                                             let uu____6573 =
                                               let uu____6574 =
                                                 let uu____6585 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6585)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6574
                                                in
                                             let uu____6608 =
                                               let uu____6611 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6611
                                                in
                                             (uu____6573, uu____6608,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6566
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____6618 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6618);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6648 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6648  in
           let uu____6649 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____6649 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6661 =
                    let uu____6668 =
                      let uu____6669 =
                        let uu____6670 =
                          let uu____6671 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6671
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____6670  in
                      varops.mk_unique uu____6669  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6668)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6661  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6676 ->
           let uu____6691 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6691 with
            | (head1,args_e) ->
                let uu____6732 =
                  let uu____6745 =
                    let uu____6746 = FStar_Syntax_Subst.compress head1  in
                    uu____6746.FStar_Syntax_Syntax.n  in
                  (uu____6745, args_e)  in
                (match uu____6732 with
                 | uu____6761 when head_redex env head1 ->
                     let uu____6774 = whnf env t  in
                     encode_term uu____6774 env
                 | uu____6775 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6794 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6808;
                       FStar_Syntax_Syntax.vars = uu____6809;_},uu____6810),uu____6811::
                    (v1,uu____6813)::(v2,uu____6815)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6866 = encode_term v1 env  in
                     (match uu____6866 with
                      | (v11,decls1) ->
                          let uu____6877 = encode_term v2 env  in
                          (match uu____6877 with
                           | (v21,decls2) ->
                               let uu____6888 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6888,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6892::(v1,uu____6894)::(v2,uu____6896)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6943 = encode_term v1 env  in
                     (match uu____6943 with
                      | (v11,decls1) ->
                          let uu____6954 = encode_term v2 env  in
                          (match uu____6954 with
                           | (v21,decls2) ->
                               let uu____6965 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6965,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6969)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6995)::(rng,uu____6997)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7032) ->
                     let e0 =
                       let uu____7050 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7050
                        in
                     ((let uu____7058 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7058
                       then
                         let uu____7059 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7059
                       else ());
                      (let e =
                         let uu____7064 =
                           let uu____7065 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7066 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7065
                             uu____7066
                            in
                         uu____7064 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7075),(arg,uu____7077)::[]) -> encode_term arg env
                 | uu____7102 ->
                     let uu____7115 = encode_args args_e env  in
                     (match uu____7115 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7170 = encode_term head1 env  in
                            match uu____7170 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7234 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7234 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7312  ->
                                                 fun uu____7313  ->
                                                   match (uu____7312,
                                                           uu____7313)
                                                   with
                                                   | ((bv,uu____7335),
                                                      (a,uu____7337)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7355 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7355
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7360 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7360 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7375 =
                                                   let uu____7382 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7391 =
                                                     let uu____7392 =
                                                       let uu____7393 =
                                                         let uu____7394 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7394
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7393
                                                        in
                                                     varops.mk_unique
                                                       uu____7392
                                                      in
                                                   (uu____7382,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7391)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7375
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7411 = lookup_free_var_sym env fv  in
                            match uu____7411 with
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
                                   FStar_Syntax_Syntax.pos = uu____7443;
                                   FStar_Syntax_Syntax.vars = uu____7444;_},uu____7445)
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
                                   FStar_Syntax_Syntax.pos = uu____7456;
                                   FStar_Syntax_Syntax.vars = uu____7457;_},uu____7458)
                                ->
                                let uu____7463 =
                                  let uu____7464 =
                                    let uu____7469 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7469
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7464
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7463
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7499 =
                                  let uu____7500 =
                                    let uu____7505 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7505
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7500
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7499
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7534,(FStar_Util.Inl t1,uu____7536),uu____7537)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7586,(FStar_Util.Inr c,uu____7588),uu____7589)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7638 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7665 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7665
                                  in
                               let uu____7666 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7666 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7682;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7683;_},uu____7684)
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
                                     | uu____7698 ->
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
           let uu____7747 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7747 with
            | (bs1,body1,opening) ->
                let fallback uu____7770 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7777 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7777, [decl])  in
                let is_impure rc =
                  let uu____7784 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7784 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7794 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____7794
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7812 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7812
                  then
                    let uu____7815 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7815
                  else
                    (let uu____7817 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7817
                     then
                       let uu____7820 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7820
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7827 =
                         let uu____7832 =
                           let uu____7833 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7833
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7832)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7827);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7835 =
                       (is_impure rc) &&
                         (let uu____7837 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____7837)
                        in
                     if uu____7835
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____7844 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7844 with
                        | (vars,guards,envbody,decls,uu____7869) ->
                            let body2 =
                              let uu____7883 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____7883
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____7885 = encode_term body2 envbody  in
                            (match uu____7885 with
                             | (body3,decls') ->
                                 let uu____7896 =
                                   let uu____7905 = codomain_eff rc  in
                                   match uu____7905 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7924 = encode_term tfun env
                                          in
                                       (match uu____7924 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7896 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7956 =
                                          let uu____7967 =
                                            let uu____7968 =
                                              let uu____7973 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7973, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7968
                                             in
                                          ([], vars, uu____7967)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____7956
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
                                            let uu____7985 =
                                              let uu____7988 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____7988
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____7985
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8007 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8007 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8015 =
                                             let uu____8016 =
                                               let uu____8023 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8023)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8016
                                              in
                                           (uu____8015,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8034 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8034 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8045 =
                                                    let uu____8046 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8046 = cache_size
                                                     in
                                                  if uu____8045
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
                                                    let uu____8062 =
                                                      let uu____8063 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8063
                                                       in
                                                    varops.mk_unique
                                                      uu____8062
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
                                                  let uu____8070 =
                                                    let uu____8077 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8077)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8070
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
                                                      let uu____8095 =
                                                        let uu____8096 =
                                                          let uu____8103 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8103,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8096
                                                         in
                                                      [uu____8095]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8116 =
                                                    let uu____8123 =
                                                      let uu____8124 =
                                                        let uu____8135 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8135)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8124
                                                       in
                                                    (uu____8123,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8116
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
                                                ((let uu____8152 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8152);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8155,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8156;
                          FStar_Syntax_Syntax.lbunivs = uu____8157;
                          FStar_Syntax_Syntax.lbtyp = uu____8158;
                          FStar_Syntax_Syntax.lbeff = uu____8159;
                          FStar_Syntax_Syntax.lbdef = uu____8160;
                          FStar_Syntax_Syntax.lbattrs = uu____8161;
                          FStar_Syntax_Syntax.lbpos = uu____8162;_}::uu____8163),uu____8164)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8194;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8196;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8198;
                FStar_Syntax_Syntax.lbpos = uu____8199;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8223 ->
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
              let uu____8293 =
                let uu____8298 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8298 env  in
              match uu____8293 with
              | (ee1,decls1) ->
                  let uu____8319 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8319 with
                   | (xs,e21) ->
                       let uu____8344 = FStar_List.hd xs  in
                       (match uu____8344 with
                        | (x1,uu____8358) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8360 = encode_body e21 env'  in
                            (match uu____8360 with
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
            let uu____8392 =
              let uu____8399 =
                let uu____8400 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8400  in
              gen_term_var env uu____8399  in
            match uu____8392 with
            | (scrsym,scr',env1) ->
                let uu____8408 = encode_term e env1  in
                (match uu____8408 with
                 | (scr,decls) ->
                     let uu____8419 =
                       let encode_branch b uu____8444 =
                         match uu____8444 with
                         | (else_case,decls1) ->
                             let uu____8463 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8463 with
                              | (p,w,br) ->
                                  let uu____8489 = encode_pat env1 p  in
                                  (match uu____8489 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8526  ->
                                                   match uu____8526 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8533 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8555 =
                                               encode_term w1 env2  in
                                             (match uu____8555 with
                                              | (w2,decls2) ->
                                                  let uu____8568 =
                                                    let uu____8569 =
                                                      let uu____8574 =
                                                        let uu____8575 =
                                                          let uu____8580 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8580)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8575
                                                         in
                                                      (guard, uu____8574)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8569
                                                     in
                                                  (uu____8568, decls2))
                                          in
                                       (match uu____8533 with
                                        | (guard1,decls2) ->
                                            let uu____8593 =
                                              encode_br br env2  in
                                            (match uu____8593 with
                                             | (br1,decls3) ->
                                                 let uu____8606 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8606,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8419 with
                      | (match_tm,decls1) ->
                          let uu____8625 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8625, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____8665 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____8665
       then
         let uu____8666 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8666
       else ());
      (let uu____8668 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8668 with
       | (vars,pat_term) ->
           let uu____8685 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8738  ->
                     fun v1  ->
                       match uu____8738 with
                       | (env1,vars1) ->
                           let uu____8790 = gen_term_var env1 v1  in
                           (match uu____8790 with
                            | (xx,uu____8812,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8685 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8891 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8892 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8893 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8901 = encode_const c env1  in
                      (match uu____8901 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8915::uu____8916 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8919 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8942 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____8942 with
                        | (uu____8949,uu____8950::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8953 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8986  ->
                                  match uu____8986 with
                                  | (arg,uu____8994) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9000 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9000))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9027) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9058 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9081 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9125  ->
                                  match uu____9125 with
                                  | (arg,uu____9139) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9145 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9145))
                         in
                      FStar_All.pipe_right uu____9081 FStar_List.flatten
                   in
                let pat_term1 uu____9173 = encode_term pat_term env1  in
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
      let uu____9183 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9221  ->
                fun uu____9222  ->
                  match (uu____9221, uu____9222) with
                  | ((tms,decls),(t,uu____9258)) ->
                      let uu____9279 = encode_term t env  in
                      (match uu____9279 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9183 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9336 = FStar_Syntax_Util.list_elements e  in
        match uu____9336 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9357 =
          let uu____9372 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9372 FStar_Syntax_Util.head_and_args  in
        match uu____9357 with
        | (head1,args) ->
            let uu____9411 =
              let uu____9424 =
                let uu____9425 = FStar_Syntax_Util.un_uinst head1  in
                uu____9425.FStar_Syntax_Syntax.n  in
              (uu____9424, args)  in
            (match uu____9411 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9439,uu____9440)::(e,uu____9442)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9477 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9513 =
            let uu____9528 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9528 FStar_Syntax_Util.head_and_args
             in
          match uu____9513 with
          | (head1,args) ->
              let uu____9569 =
                let uu____9582 =
                  let uu____9583 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9583.FStar_Syntax_Syntax.n  in
                (uu____9582, args)  in
              (match uu____9569 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9600)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9627 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9649 = smt_pat_or1 t1  in
            (match uu____9649 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9665 = list_elements1 e  in
                 FStar_All.pipe_right uu____9665
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9683 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9683
                           (FStar_List.map one_pat)))
             | uu____9694 ->
                 let uu____9699 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9699])
        | uu____9720 ->
            let uu____9723 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9723]
         in
      let uu____9744 =
        let uu____9763 =
          let uu____9764 = FStar_Syntax_Subst.compress t  in
          uu____9764.FStar_Syntax_Syntax.n  in
        match uu____9763 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9803 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9803 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9846;
                        FStar_Syntax_Syntax.effect_name = uu____9847;
                        FStar_Syntax_Syntax.result_typ = uu____9848;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9850)::(post,uu____9852)::(pats,uu____9854)::[];
                        FStar_Syntax_Syntax.flags = uu____9855;_}
                      ->
                      let uu____9896 = lemma_pats pats  in
                      (binders1, pre, post, uu____9896)
                  | uu____9913 -> failwith "impos"))
        | uu____9932 -> failwith "Impos"  in
      match uu____9744 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___114_9980 = env  in
            {
              bindings = (uu___114_9980.bindings);
              depth = (uu___114_9980.depth);
              tcenv = (uu___114_9980.tcenv);
              warn = (uu___114_9980.warn);
              cache = (uu___114_9980.cache);
              nolabels = (uu___114_9980.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___114_9980.encode_non_total_function_typ);
              current_module_name = (uu___114_9980.current_module_name)
            }  in
          let uu____9981 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9981 with
           | (vars,guards,env2,decls,uu____10006) ->
               let uu____10019 =
                 let uu____10034 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10088 =
                             let uu____10099 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10099
                               FStar_List.unzip
                              in
                           match uu____10088 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10034 FStar_List.unzip  in
               (match uu____10019 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___115_10251 = env2  in
                      {
                        bindings = (uu___115_10251.bindings);
                        depth = (uu___115_10251.depth);
                        tcenv = (uu___115_10251.tcenv);
                        warn = (uu___115_10251.warn);
                        cache = (uu___115_10251.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___115_10251.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___115_10251.encode_non_total_function_typ);
                        current_module_name =
                          (uu___115_10251.current_module_name)
                      }  in
                    let uu____10252 =
                      let uu____10257 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10257 env3  in
                    (match uu____10252 with
                     | (pre1,decls'') ->
                         let uu____10264 =
                           let uu____10269 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10269 env3  in
                         (match uu____10264 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10279 =
                                let uu____10280 =
                                  let uu____10291 =
                                    let uu____10292 =
                                      let uu____10297 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10297, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10292
                                     in
                                  (pats, vars, uu____10291)  in
                                FStar_SMTEncoding_Util.mkForall uu____10280
                                 in
                              (uu____10279, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____10310 = FStar_Syntax_Util.head_and_args t  in
      match uu____10310 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10369::(x,uu____10371)::(t1,uu____10373)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10420 = encode_term x env  in
               (match uu____10420 with
                | (x1,decls) ->
                    let uu____10433 = encode_term t1 env  in
                    (match uu____10433 with
                     | (t2,decls') ->
                         let uu____10446 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10446, (FStar_List.append decls decls'))))
           | uu____10449 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10472 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10472
        then
          let uu____10473 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10474 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10473 uu____10474
        else ()  in
      let enc f r l =
        let uu____10507 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10535 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10535 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10507 with
        | (decls,args) ->
            let uu____10564 =
              let uu___116_10565 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___116_10565.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___116_10565.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10564, decls)
         in
      let const_op f r uu____10596 =
        let uu____10609 = f r  in (uu____10609, [])  in
      let un_op f l =
        let uu____10628 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10628  in
      let bin_op f uu___90_10644 =
        match uu___90_10644 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10655 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10689 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10712  ->
                 match uu____10712 with
                 | (t,uu____10726) ->
                     let uu____10727 = encode_formula t env  in
                     (match uu____10727 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10689 with
        | (decls,phis) ->
            let uu____10756 =
              let uu___117_10757 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___117_10757.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___117_10757.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10756, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10818  ->
               match uu____10818 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10837) -> false
                    | uu____10838 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10853 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10853
        else
          (let uu____10867 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10867 r rf)
         in
      let mk_imp1 r uu___91_10892 =
        match uu___91_10892 with
        | (lhs,uu____10898)::(rhs,uu____10900)::[] ->
            let uu____10927 = encode_formula rhs env  in
            (match uu____10927 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10942) ->
                      (l1, decls1)
                  | uu____10947 ->
                      let uu____10948 = encode_formula lhs env  in
                      (match uu____10948 with
                       | (l2,decls2) ->
                           let uu____10959 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10959, (FStar_List.append decls1 decls2)))))
        | uu____10962 -> failwith "impossible"  in
      let mk_ite r uu___92_10983 =
        match uu___92_10983 with
        | (guard,uu____10989)::(_then,uu____10991)::(_else,uu____10993)::[]
            ->
            let uu____11030 = encode_formula guard env  in
            (match uu____11030 with
             | (g,decls1) ->
                 let uu____11041 = encode_formula _then env  in
                 (match uu____11041 with
                  | (t,decls2) ->
                      let uu____11052 = encode_formula _else env  in
                      (match uu____11052 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11066 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11091 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11091  in
      let connectives =
        let uu____11109 =
          let uu____11122 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11122)  in
        let uu____11139 =
          let uu____11154 =
            let uu____11167 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11167)  in
          let uu____11184 =
            let uu____11199 =
              let uu____11214 =
                let uu____11227 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11227)  in
              let uu____11244 =
                let uu____11259 =
                  let uu____11274 =
                    let uu____11287 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11287)  in
                  [uu____11274;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11259  in
              uu____11214 :: uu____11244  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11199  in
          uu____11154 :: uu____11184  in
        uu____11109 :: uu____11139  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11608 = encode_formula phi' env  in
            (match uu____11608 with
             | (phi2,decls) ->
                 let uu____11619 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11619, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11620 ->
            let uu____11627 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11627 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11666 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11666 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11678;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11680;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11682;
                 FStar_Syntax_Syntax.lbpos = uu____11683;_}::[]),e2)
            ->
            let uu____11707 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11707 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11754::(x,uu____11756)::(t,uu____11758)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11805 = encode_term x env  in
                 (match uu____11805 with
                  | (x1,decls) ->
                      let uu____11816 = encode_term t env  in
                      (match uu____11816 with
                       | (t1,decls') ->
                           let uu____11827 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11827, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11832)::(msg,uu____11834)::(phi2,uu____11836)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11881 =
                   let uu____11886 =
                     let uu____11887 = FStar_Syntax_Subst.compress r  in
                     uu____11887.FStar_Syntax_Syntax.n  in
                   let uu____11890 =
                     let uu____11891 = FStar_Syntax_Subst.compress msg  in
                     uu____11891.FStar_Syntax_Syntax.n  in
                   (uu____11886, uu____11890)  in
                 (match uu____11881 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11900))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11906 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11913)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11938 when head_redex env head2 ->
                 let uu____11951 = whnf env phi1  in
                 encode_formula uu____11951 env
             | uu____11952 ->
                 let uu____11965 = encode_term phi1 env  in
                 (match uu____11965 with
                  | (tt,decls) ->
                      let uu____11976 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___118_11979 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___118_11979.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___118_11979.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____11976, decls)))
        | uu____11980 ->
            let uu____11981 = encode_term phi1 env  in
            (match uu____11981 with
             | (tt,decls) ->
                 let uu____11992 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___119_11995 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___119_11995.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___119_11995.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____11992, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12031 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12031 with
        | (vars,guards,env2,decls,uu____12070) ->
            let uu____12083 =
              let uu____12096 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12148 =
                          let uu____12159 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12199  ->
                                    match uu____12199 with
                                    | (t,uu____12213) ->
                                        encode_smt_pattern t
                                          (let uu___120_12219 = env2  in
                                           {
                                             bindings =
                                               (uu___120_12219.bindings);
                                             depth = (uu___120_12219.depth);
                                             tcenv = (uu___120_12219.tcenv);
                                             warn = (uu___120_12219.warn);
                                             cache = (uu___120_12219.cache);
                                             nolabels =
                                               (uu___120_12219.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___120_12219.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___120_12219.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12159 FStar_List.unzip
                           in
                        match uu____12148 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12096 FStar_List.unzip  in
            (match uu____12083 with
             | (pats,decls') ->
                 let uu____12328 = encode_formula body env2  in
                 (match uu____12328 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12360;
                             FStar_SMTEncoding_Term.rng = uu____12361;_}::[])::[]
                            when
                            let uu____12376 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12376 = gf -> []
                        | uu____12377 -> guards  in
                      let uu____12382 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12382, body1,
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
                (fun uu____12442  ->
                   match uu____12442 with
                   | (x,uu____12448) ->
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
               let uu____12456 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12468 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12468) uu____12456 tl1
                in
             let uu____12471 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12498  ->
                       match uu____12498 with
                       | (b,uu____12504) ->
                           let uu____12505 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12505))
                in
             (match uu____12471 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12511) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12525 =
                    let uu____12530 =
                      let uu____12531 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12531
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12530)
                     in
                  FStar_Errors.log_issue pos uu____12525)
          in
       let uu____12532 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12532 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12541 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12599  ->
                     match uu____12599 with
                     | (l,uu____12613) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12541 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12646,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12686 = encode_q_body env vars pats body  in
             match uu____12686 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12731 =
                     let uu____12742 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12742)  in
                   FStar_SMTEncoding_Term.mkForall uu____12731
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12761 = encode_q_body env vars pats body  in
             match uu____12761 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12805 =
                   let uu____12806 =
                     let uu____12817 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12817)  in
                   FStar_SMTEncoding_Term.mkExists uu____12806
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____12805, decls))))

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
  let uu____12920 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____12920 with
  | (asym,a) ->
      let uu____12927 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____12927 with
       | (xsym,x) ->
           let uu____12934 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____12934 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____12982 =
                      let uu____12993 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____12993, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12982  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13019 =
                      let uu____13026 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13026)  in
                    FStar_SMTEncoding_Util.mkApp uu____13019  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13039 =
                    let uu____13042 =
                      let uu____13045 =
                        let uu____13048 =
                          let uu____13049 =
                            let uu____13056 =
                              let uu____13057 =
                                let uu____13068 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13068)  in
                              FStar_SMTEncoding_Util.mkForall uu____13057  in
                            (uu____13056, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13049  in
                        let uu____13085 =
                          let uu____13088 =
                            let uu____13089 =
                              let uu____13096 =
                                let uu____13097 =
                                  let uu____13108 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13108)  in
                                FStar_SMTEncoding_Util.mkForall uu____13097
                                 in
                              (uu____13096,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13089  in
                          [uu____13088]  in
                        uu____13048 :: uu____13085  in
                      xtok_decl :: uu____13045  in
                    xname_decl :: uu____13042  in
                  (xtok1, (FStar_List.length vars), uu____13039)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13205 =
                    let uu____13220 =
                      let uu____13231 =
                        let uu____13232 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13232
                         in
                      quant axy uu____13231  in
                    (FStar_Parser_Const.op_Eq, uu____13220)  in
                  let uu____13243 =
                    let uu____13260 =
                      let uu____13275 =
                        let uu____13286 =
                          let uu____13287 =
                            let uu____13288 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13288  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13287
                           in
                        quant axy uu____13286  in
                      (FStar_Parser_Const.op_notEq, uu____13275)  in
                    let uu____13299 =
                      let uu____13316 =
                        let uu____13331 =
                          let uu____13342 =
                            let uu____13343 =
                              let uu____13344 =
                                let uu____13349 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13350 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13349, uu____13350)  in
                              FStar_SMTEncoding_Util.mkLT uu____13344  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13343
                             in
                          quant xy uu____13342  in
                        (FStar_Parser_Const.op_LT, uu____13331)  in
                      let uu____13361 =
                        let uu____13378 =
                          let uu____13393 =
                            let uu____13404 =
                              let uu____13405 =
                                let uu____13406 =
                                  let uu____13411 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13412 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13411, uu____13412)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13406  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13405
                               in
                            quant xy uu____13404  in
                          (FStar_Parser_Const.op_LTE, uu____13393)  in
                        let uu____13423 =
                          let uu____13440 =
                            let uu____13455 =
                              let uu____13466 =
                                let uu____13467 =
                                  let uu____13468 =
                                    let uu____13473 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13474 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13473, uu____13474)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13468  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13467
                                 in
                              quant xy uu____13466  in
                            (FStar_Parser_Const.op_GT, uu____13455)  in
                          let uu____13485 =
                            let uu____13502 =
                              let uu____13517 =
                                let uu____13528 =
                                  let uu____13529 =
                                    let uu____13530 =
                                      let uu____13535 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13536 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13535, uu____13536)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13530
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13529
                                   in
                                quant xy uu____13528  in
                              (FStar_Parser_Const.op_GTE, uu____13517)  in
                            let uu____13547 =
                              let uu____13564 =
                                let uu____13579 =
                                  let uu____13590 =
                                    let uu____13591 =
                                      let uu____13592 =
                                        let uu____13597 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13598 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13597, uu____13598)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13592
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13591
                                     in
                                  quant xy uu____13590  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13579)
                                 in
                              let uu____13609 =
                                let uu____13626 =
                                  let uu____13641 =
                                    let uu____13652 =
                                      let uu____13653 =
                                        let uu____13654 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13654
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13653
                                       in
                                    quant qx uu____13652  in
                                  (FStar_Parser_Const.op_Minus, uu____13641)
                                   in
                                let uu____13665 =
                                  let uu____13682 =
                                    let uu____13697 =
                                      let uu____13708 =
                                        let uu____13709 =
                                          let uu____13710 =
                                            let uu____13715 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____13716 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____13715, uu____13716)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13710
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13709
                                         in
                                      quant xy uu____13708  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13697)
                                     in
                                  let uu____13727 =
                                    let uu____13744 =
                                      let uu____13759 =
                                        let uu____13770 =
                                          let uu____13771 =
                                            let uu____13772 =
                                              let uu____13777 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____13778 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____13777, uu____13778)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13772
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13771
                                           in
                                        quant xy uu____13770  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13759)
                                       in
                                    let uu____13789 =
                                      let uu____13806 =
                                        let uu____13821 =
                                          let uu____13832 =
                                            let uu____13833 =
                                              let uu____13834 =
                                                let uu____13839 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____13840 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____13839, uu____13840)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13834
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13833
                                             in
                                          quant xy uu____13832  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13821)
                                         in
                                      let uu____13851 =
                                        let uu____13868 =
                                          let uu____13883 =
                                            let uu____13894 =
                                              let uu____13895 =
                                                let uu____13896 =
                                                  let uu____13901 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____13902 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____13901, uu____13902)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13896
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13895
                                               in
                                            quant xy uu____13894  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13883)
                                           in
                                        let uu____13913 =
                                          let uu____13930 =
                                            let uu____13945 =
                                              let uu____13956 =
                                                let uu____13957 =
                                                  let uu____13958 =
                                                    let uu____13963 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____13964 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____13963,
                                                      uu____13964)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13958
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13957
                                                 in
                                              quant xy uu____13956  in
                                            (FStar_Parser_Const.op_And,
                                              uu____13945)
                                             in
                                          let uu____13975 =
                                            let uu____13992 =
                                              let uu____14007 =
                                                let uu____14018 =
                                                  let uu____14019 =
                                                    let uu____14020 =
                                                      let uu____14025 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14026 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14025,
                                                        uu____14026)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14020
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14019
                                                   in
                                                quant xy uu____14018  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14007)
                                               in
                                            let uu____14037 =
                                              let uu____14054 =
                                                let uu____14069 =
                                                  let uu____14080 =
                                                    let uu____14081 =
                                                      let uu____14082 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14082
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14081
                                                     in
                                                  quant qx uu____14080  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14069)
                                                 in
                                              [uu____14054]  in
                                            uu____13992 :: uu____14037  in
                                          uu____13930 :: uu____13975  in
                                        uu____13868 :: uu____13913  in
                                      uu____13806 :: uu____13851  in
                                    uu____13744 :: uu____13789  in
                                  uu____13682 :: uu____13727  in
                                uu____13626 :: uu____13665  in
                              uu____13564 :: uu____13609  in
                            uu____13502 :: uu____13547  in
                          uu____13440 :: uu____13485  in
                        uu____13378 :: uu____13423  in
                      uu____13316 :: uu____13361  in
                    uu____13260 :: uu____13299  in
                  uu____13205 :: uu____13243  in
                let mk1 l v1 =
                  let uu____14332 =
                    let uu____14343 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14409  ->
                              match uu____14409 with
                              | (l',uu____14425) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14343
                      (FStar_Option.map
                         (fun uu____14497  ->
                            match uu____14497 with | (uu____14520,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14332 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14605  ->
                          match uu____14605 with
                          | (l',uu____14621) -> FStar_Ident.lid_equals l l'))
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
        let uu____14663 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14663 with
        | (xxsym,xx) ->
            let uu____14670 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14670 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14680 =
                   let uu____14687 =
                     let uu____14688 =
                       let uu____14699 =
                         let uu____14700 =
                           let uu____14705 =
                             let uu____14706 =
                               let uu____14711 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14711)  in
                             FStar_SMTEncoding_Util.mkEq uu____14706  in
                           (xx_has_type, uu____14705)  in
                         FStar_SMTEncoding_Util.mkImp uu____14700  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14699)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14688  in
                   let uu____14736 =
                     let uu____14737 =
                       let uu____14738 =
                         let uu____14739 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14739  in
                       Prims.strcat module_name uu____14738  in
                     varops.mk_unique uu____14737  in
                   (uu____14687, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14736)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14680)
  
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
    let uu____14775 =
      let uu____14776 =
        let uu____14783 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14783, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14776  in
    let uu____14786 =
      let uu____14789 =
        let uu____14790 =
          let uu____14797 =
            let uu____14798 =
              let uu____14809 =
                let uu____14810 =
                  let uu____14815 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____14815)  in
                FStar_SMTEncoding_Util.mkImp uu____14810  in
              ([[typing_pred]], [xx], uu____14809)  in
            mkForall_fuel uu____14798  in
          (uu____14797, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14790  in
      [uu____14789]  in
    uu____14775 :: uu____14786  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____14857 =
      let uu____14858 =
        let uu____14865 =
          let uu____14866 =
            let uu____14877 =
              let uu____14882 =
                let uu____14885 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____14885]  in
              [uu____14882]  in
            let uu____14890 =
              let uu____14891 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14891 tt  in
            (uu____14877, [bb], uu____14890)  in
          FStar_SMTEncoding_Util.mkForall uu____14866  in
        (uu____14865, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14858  in
    let uu____14912 =
      let uu____14915 =
        let uu____14916 =
          let uu____14923 =
            let uu____14924 =
              let uu____14935 =
                let uu____14936 =
                  let uu____14941 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____14941)  in
                FStar_SMTEncoding_Util.mkImp uu____14936  in
              ([[typing_pred]], [xx], uu____14935)  in
            mkForall_fuel uu____14924  in
          (uu____14923, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14916  in
      [uu____14915]  in
    uu____14857 :: uu____14912  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____14991 =
        let uu____14992 =
          let uu____14999 =
            let uu____15002 =
              let uu____15005 =
                let uu____15008 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15009 =
                  let uu____15012 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15012]  in
                uu____15008 :: uu____15009  in
              tt :: uu____15005  in
            tt :: uu____15002  in
          ("Prims.Precedes", uu____14999)  in
        FStar_SMTEncoding_Util.mkApp uu____14992  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14991  in
    let precedes_y_x =
      let uu____15016 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15016  in
    let uu____15019 =
      let uu____15020 =
        let uu____15027 =
          let uu____15028 =
            let uu____15039 =
              let uu____15044 =
                let uu____15047 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15047]  in
              [uu____15044]  in
            let uu____15052 =
              let uu____15053 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15053 tt  in
            (uu____15039, [bb], uu____15052)  in
          FStar_SMTEncoding_Util.mkForall uu____15028  in
        (uu____15027, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15020  in
    let uu____15074 =
      let uu____15077 =
        let uu____15078 =
          let uu____15085 =
            let uu____15086 =
              let uu____15097 =
                let uu____15098 =
                  let uu____15103 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15103)  in
                FStar_SMTEncoding_Util.mkImp uu____15098  in
              ([[typing_pred]], [xx], uu____15097)  in
            mkForall_fuel uu____15086  in
          (uu____15085, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15078  in
      let uu____15128 =
        let uu____15131 =
          let uu____15132 =
            let uu____15139 =
              let uu____15140 =
                let uu____15151 =
                  let uu____15152 =
                    let uu____15157 =
                      let uu____15158 =
                        let uu____15161 =
                          let uu____15164 =
                            let uu____15167 =
                              let uu____15168 =
                                let uu____15173 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15174 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15173, uu____15174)  in
                              FStar_SMTEncoding_Util.mkGT uu____15168  in
                            let uu____15175 =
                              let uu____15178 =
                                let uu____15179 =
                                  let uu____15184 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15185 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15184, uu____15185)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15179  in
                              let uu____15186 =
                                let uu____15189 =
                                  let uu____15190 =
                                    let uu____15195 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15196 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15195, uu____15196)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15190  in
                                [uu____15189]  in
                              uu____15178 :: uu____15186  in
                            uu____15167 :: uu____15175  in
                          typing_pred_y :: uu____15164  in
                        typing_pred :: uu____15161  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15158  in
                    (uu____15157, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15152  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15151)
                 in
              mkForall_fuel uu____15140  in
            (uu____15139,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15132  in
        [uu____15131]  in
      uu____15077 :: uu____15128  in
    uu____15019 :: uu____15074  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15242 =
      let uu____15243 =
        let uu____15250 =
          let uu____15251 =
            let uu____15262 =
              let uu____15267 =
                let uu____15270 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15270]  in
              [uu____15267]  in
            let uu____15275 =
              let uu____15276 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15276 tt  in
            (uu____15262, [bb], uu____15275)  in
          FStar_SMTEncoding_Util.mkForall uu____15251  in
        (uu____15250, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15243  in
    let uu____15297 =
      let uu____15300 =
        let uu____15301 =
          let uu____15308 =
            let uu____15309 =
              let uu____15320 =
                let uu____15321 =
                  let uu____15326 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15326)  in
                FStar_SMTEncoding_Util.mkImp uu____15321  in
              ([[typing_pred]], [xx], uu____15320)  in
            mkForall_fuel uu____15309  in
          (uu____15308, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15301  in
      [uu____15300]  in
    uu____15242 :: uu____15297  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15379 =
      let uu____15380 =
        let uu____15387 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15387, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15380  in
    [uu____15379]  in
  let mk_and_interp env conj uu____15399 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15424 =
      let uu____15425 =
        let uu____15432 =
          let uu____15433 =
            let uu____15444 =
              let uu____15445 =
                let uu____15450 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15450, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15445  in
            ([[l_and_a_b]], [aa; bb], uu____15444)  in
          FStar_SMTEncoding_Util.mkForall uu____15433  in
        (uu____15432, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15425  in
    [uu____15424]  in
  let mk_or_interp env disj uu____15488 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15513 =
      let uu____15514 =
        let uu____15521 =
          let uu____15522 =
            let uu____15533 =
              let uu____15534 =
                let uu____15539 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15539, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15534  in
            ([[l_or_a_b]], [aa; bb], uu____15533)  in
          FStar_SMTEncoding_Util.mkForall uu____15522  in
        (uu____15521, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15514  in
    [uu____15513]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15602 =
      let uu____15603 =
        let uu____15610 =
          let uu____15611 =
            let uu____15622 =
              let uu____15623 =
                let uu____15628 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15628, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15623  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15622)  in
          FStar_SMTEncoding_Util.mkForall uu____15611  in
        (uu____15610, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15603  in
    [uu____15602]  in
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
    let uu____15701 =
      let uu____15702 =
        let uu____15709 =
          let uu____15710 =
            let uu____15721 =
              let uu____15722 =
                let uu____15727 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15727, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15722  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15721)  in
          FStar_SMTEncoding_Util.mkForall uu____15710  in
        (uu____15709, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15702  in
    [uu____15701]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15798 =
      let uu____15799 =
        let uu____15806 =
          let uu____15807 =
            let uu____15818 =
              let uu____15819 =
                let uu____15824 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____15824, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15819  in
            ([[l_imp_a_b]], [aa; bb], uu____15818)  in
          FStar_SMTEncoding_Util.mkForall uu____15807  in
        (uu____15806, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15799  in
    [uu____15798]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15887 =
      let uu____15888 =
        let uu____15895 =
          let uu____15896 =
            let uu____15907 =
              let uu____15908 =
                let uu____15913 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____15913, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15908  in
            ([[l_iff_a_b]], [aa; bb], uu____15907)  in
          FStar_SMTEncoding_Util.mkForall uu____15896  in
        (uu____15895, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15888  in
    [uu____15887]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____15965 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15965  in
    let uu____15968 =
      let uu____15969 =
        let uu____15976 =
          let uu____15977 =
            let uu____15988 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____15988)  in
          FStar_SMTEncoding_Util.mkForall uu____15977  in
        (uu____15976, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15969  in
    [uu____15968]  in
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
      let uu____16048 =
        let uu____16055 =
          let uu____16058 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16058]  in
        ("Valid", uu____16055)  in
      FStar_SMTEncoding_Util.mkApp uu____16048  in
    let uu____16061 =
      let uu____16062 =
        let uu____16069 =
          let uu____16070 =
            let uu____16081 =
              let uu____16082 =
                let uu____16087 =
                  let uu____16088 =
                    let uu____16099 =
                      let uu____16104 =
                        let uu____16107 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16107]  in
                      [uu____16104]  in
                    let uu____16112 =
                      let uu____16113 =
                        let uu____16118 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16118, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16113  in
                    (uu____16099, [xx1], uu____16112)  in
                  FStar_SMTEncoding_Util.mkForall uu____16088  in
                (uu____16087, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16082  in
            ([[l_forall_a_b]], [aa; bb], uu____16081)  in
          FStar_SMTEncoding_Util.mkForall uu____16070  in
        (uu____16069, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16062  in
    [uu____16061]  in
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
      let uu____16200 =
        let uu____16207 =
          let uu____16210 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16210]  in
        ("Valid", uu____16207)  in
      FStar_SMTEncoding_Util.mkApp uu____16200  in
    let uu____16213 =
      let uu____16214 =
        let uu____16221 =
          let uu____16222 =
            let uu____16233 =
              let uu____16234 =
                let uu____16239 =
                  let uu____16240 =
                    let uu____16251 =
                      let uu____16256 =
                        let uu____16259 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16259]  in
                      [uu____16256]  in
                    let uu____16264 =
                      let uu____16265 =
                        let uu____16270 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16270, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16265  in
                    (uu____16251, [xx1], uu____16264)  in
                  FStar_SMTEncoding_Util.mkExists uu____16240  in
                (uu____16239, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16234  in
            ([[l_exists_a_b]], [aa; bb], uu____16233)  in
          FStar_SMTEncoding_Util.mkForall uu____16222  in
        (uu____16221, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16214  in
    [uu____16213]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16330 =
      let uu____16331 =
        let uu____16338 =
          let uu____16339 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16339 range_ty  in
        let uu____16340 = varops.mk_unique "typing_range_const"  in
        (uu____16338, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16340)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16331  in
    [uu____16330]  in
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
        let uu____16374 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16374 x1 t  in
      let uu____16375 =
        let uu____16386 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16386)  in
      FStar_SMTEncoding_Util.mkForall uu____16375  in
    let uu____16409 =
      let uu____16410 =
        let uu____16417 =
          let uu____16418 =
            let uu____16429 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16429)  in
          FStar_SMTEncoding_Util.mkForall uu____16418  in
        (uu____16417,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16410  in
    [uu____16409]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____16479 =
      let uu____16480 =
        let uu____16487 =
          let uu____16488 =
            let uu____16503 =
              let uu____16504 =
                let uu____16509 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____16510 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____16509, uu____16510)  in
              FStar_SMTEncoding_Util.mkAnd uu____16504  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16503)
             in
          FStar_SMTEncoding_Util.mkForall' uu____16488  in
        (uu____16487,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16480  in
    [uu____16479]  in
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
          let uu____16856 =
            FStar_Util.find_opt
              (fun uu____16882  ->
                 match uu____16882 with
                 | (l,uu____16894) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16856 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16919,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16955 = encode_function_type_as_formula t env  in
        match uu____16955 with
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
              let uu____16995 =
                ((let uu____16998 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____16998) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____16995
              then
                let arg_sorts =
                  let uu____17008 =
                    let uu____17009 = FStar_Syntax_Subst.compress t_norm  in
                    uu____17009.FStar_Syntax_Syntax.n  in
                  match uu____17008 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17015) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____17045  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____17050 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____17052 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____17052 with
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
                (let uu____17085 = prims.is lid  in
                 if uu____17085
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17093 = prims.mk lid vname  in
                   match uu____17093 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17120 =
                      let uu____17131 = curried_arrow_formals_comp t_norm  in
                      match uu____17131 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17149 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17149
                            then
                              let uu____17150 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___121_17153 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___121_17153.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___121_17153.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___121_17153.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___121_17153.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___121_17153.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___121_17153.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___121_17153.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___121_17153.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___121_17153.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___121_17153.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___121_17153.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___121_17153.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___121_17153.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___121_17153.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___121_17153.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___121_17153.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___121_17153.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___121_17153.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___121_17153.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___121_17153.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___121_17153.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___121_17153.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___121_17153.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___121_17153.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___121_17153.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___121_17153.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___121_17153.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___121_17153.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___121_17153.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___121_17153.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___121_17153.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___121_17153.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___121_17153.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___121_17153.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___121_17153.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___121_17153.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17150
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17165 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17165)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17120 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____17215 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____17215 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17240 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___93_17282  ->
                                       match uu___93_17282 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17286 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17286 with
                                            | (uu____17307,(xxsym,uu____17309))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17327 =
                                                  let uu____17328 =
                                                    let uu____17335 =
                                                      let uu____17336 =
                                                        let uu____17347 =
                                                          let uu____17348 =
                                                            let uu____17353 =
                                                              let uu____17354
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17354
                                                               in
                                                            (vapp,
                                                              uu____17353)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17348
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17347)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17336
                                                       in
                                                    (uu____17335,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17328
                                                   in
                                                [uu____17327])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17373 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17373 with
                                            | (uu____17394,(xxsym,uu____17396))
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
                                                let uu____17419 =
                                                  let uu____17420 =
                                                    let uu____17427 =
                                                      let uu____17428 =
                                                        let uu____17439 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17439)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17428
                                                       in
                                                    (uu____17427,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17420
                                                   in
                                                [uu____17419])
                                       | uu____17456 -> []))
                                in
                             let uu____17457 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17457 with
                              | (vars,guards,env',decls1,uu____17484) ->
                                  let uu____17497 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17506 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17506, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17508 =
                                          encode_formula p env'  in
                                        (match uu____17508 with
                                         | (g,ds) ->
                                             let uu____17519 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17519,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17497 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17532 =
                                           let uu____17539 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17539)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17532
                                          in
                                       let uu____17548 =
                                         let vname_decl =
                                           let uu____17556 =
                                             let uu____17567 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17577  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17567,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17556
                                            in
                                         let uu____17586 =
                                           let env2 =
                                             let uu___122_17592 = env1  in
                                             {
                                               bindings =
                                                 (uu___122_17592.bindings);
                                               depth = (uu___122_17592.depth);
                                               tcenv = (uu___122_17592.tcenv);
                                               warn = (uu___122_17592.warn);
                                               cache = (uu___122_17592.cache);
                                               nolabels =
                                                 (uu___122_17592.nolabels);
                                               use_zfuel_name =
                                                 (uu___122_17592.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___122_17592.current_module_name)
                                             }  in
                                           let uu____17593 =
                                             let uu____17594 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17594
                                              in
                                           if uu____17593
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17586 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17609::uu____17610 ->
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
                                                     let uu____17650 =
                                                       let uu____17661 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17661)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17650
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17688 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17691 =
                                               match formals with
                                               | [] ->
                                                   let uu____17708 =
                                                     let uu____17709 =
                                                       let uu____17712 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17712
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____17709
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17708)
                                               | uu____17721 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17728 =
                                                       let uu____17735 =
                                                         let uu____17736 =
                                                           let uu____17747 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17747)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17736
                                                          in
                                                       (uu____17735,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17728
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17691 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17548 with
                                        | (decls2,env2) ->
                                            let uu____17790 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17798 =
                                                encode_term res_t1 env'  in
                                              match uu____17798 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17811 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17811, decls)
                                               in
                                            (match uu____17790 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17822 =
                                                     let uu____17829 =
                                                       let uu____17830 =
                                                         let uu____17841 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17841)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17830
                                                        in
                                                     (uu____17829,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17822
                                                    in
                                                 let freshness =
                                                   let uu____17857 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17857
                                                   then
                                                     let uu____17862 =
                                                       let uu____17863 =
                                                         let uu____17874 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17885 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17874,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17885)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17863
                                                        in
                                                     let uu____17888 =
                                                       let uu____17891 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17891]  in
                                                     uu____17862 ::
                                                       uu____17888
                                                   else []  in
                                                 let g =
                                                   let uu____17896 =
                                                     let uu____17899 =
                                                       let uu____17902 =
                                                         let uu____17905 =
                                                           let uu____17908 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17908
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17905
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17902
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17899
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17896
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
          let uu____17933 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____17933 with
          | FStar_Pervasives_Native.None  ->
              let uu____17944 = encode_free_var false env x t t_norm []  in
              (match uu____17944 with
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
            let uu____17997 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____17997 with
            | (decls,env1) ->
                let uu____18016 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18016
                then
                  let uu____18023 =
                    let uu____18026 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18026  in
                  (uu____18023, env1)
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
             (fun uu____18078  ->
                fun lb  ->
                  match uu____18078 with
                  | (decls,env1) ->
                      let uu____18098 =
                        let uu____18105 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18105
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18098 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18126 = FStar_Syntax_Util.head_and_args t  in
    match uu____18126 with
    | (hd1,args) ->
        let uu____18163 =
          let uu____18164 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18164.FStar_Syntax_Syntax.n  in
        (match uu____18163 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18168,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18187 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18209  ->
      fun quals  ->
        match uu____18209 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18285 = FStar_Util.first_N nbinders formals  in
              match uu____18285 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18366  ->
                         fun uu____18367  ->
                           match (uu____18366, uu____18367) with
                           | ((formal,uu____18385),(binder,uu____18387)) ->
                               let uu____18396 =
                                 let uu____18403 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18403)  in
                               FStar_Syntax_Syntax.NT uu____18396) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18411 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18442  ->
                              match uu____18442 with
                              | (x,i) ->
                                  let uu____18453 =
                                    let uu___123_18454 = x  in
                                    let uu____18455 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___123_18454.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___123_18454.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18455
                                    }  in
                                  (uu____18453, i)))
                       in
                    FStar_All.pipe_right uu____18411
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18473 =
                      let uu____18474 = FStar_Syntax_Subst.compress body  in
                      let uu____18475 =
                        let uu____18476 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18476
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18474
                        uu____18475
                       in
                    uu____18473 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18537 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18537
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___124_18540 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___124_18540.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___124_18540.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___124_18540.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___124_18540.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___124_18540.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___124_18540.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___124_18540.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___124_18540.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___124_18540.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___124_18540.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___124_18540.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___124_18540.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___124_18540.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___124_18540.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___124_18540.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___124_18540.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___124_18540.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___124_18540.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___124_18540.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___124_18540.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___124_18540.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___124_18540.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___124_18540.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___124_18540.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___124_18540.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___124_18540.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___124_18540.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___124_18540.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___124_18540.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___124_18540.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___124_18540.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___124_18540.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___124_18540.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___124_18540.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___124_18540.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___124_18540.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18573 = FStar_Syntax_Util.abs_formals e  in
                match uu____18573 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18637::uu____18638 ->
                         let uu____18653 =
                           let uu____18654 =
                             let uu____18657 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18657
                              in
                           uu____18654.FStar_Syntax_Syntax.n  in
                         (match uu____18653 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18700 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18700 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18742 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18742
                                   then
                                     let uu____18777 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18777 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18871  ->
                                                   fun uu____18872  ->
                                                     match (uu____18871,
                                                             uu____18872)
                                                     with
                                                     | ((x,uu____18890),
                                                        (b,uu____18892)) ->
                                                         let uu____18901 =
                                                           let uu____18908 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____18908)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18901)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____18910 =
                                            let uu____18931 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____18931)
                                             in
                                          (uu____18910, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18999 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____18999 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19088) ->
                              let uu____19093 =
                                let uu____19114 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19114  in
                              (uu____19093, true)
                          | uu____19179 when Prims.op_Negation norm1 ->
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
                          | uu____19181 ->
                              let uu____19182 =
                                let uu____19183 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19184 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19183
                                  uu____19184
                                 in
                              failwith uu____19182)
                     | uu____19209 ->
                         let rec aux' t_norm2 =
                           let uu____19234 =
                             let uu____19235 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19235.FStar_Syntax_Syntax.n  in
                           match uu____19234 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19276 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19276 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19304 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19304 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19384)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19389 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19445 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19445
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19457 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19520  ->
                            fun lb  ->
                              match uu____19520 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19575 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19575
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19578 =
                                      let uu____19587 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19587
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19578 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19457 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____19702 =
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
                        | uu____19708 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19716 = mk_fv ()  in
                                   mk_Apply uu____19716 vars)
                            else
                              (let uu____19718 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____19718)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19770;
                             FStar_Syntax_Syntax.lbeff = uu____19771;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____19773;
                             FStar_Syntax_Syntax.lbpos = uu____19774;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____19798 =
                              let uu____19805 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____19805 with
                              | (tcenv',uu____19823,e_t) ->
                                  let uu____19829 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19840 -> failwith "Impossible"
                                     in
                                  (match uu____19829 with
                                   | (e1,t_norm1) ->
                                       ((let uu___127_19856 = env2  in
                                         {
                                           bindings =
                                             (uu___127_19856.bindings);
                                           depth = (uu___127_19856.depth);
                                           tcenv = tcenv';
                                           warn = (uu___127_19856.warn);
                                           cache = (uu___127_19856.cache);
                                           nolabels =
                                             (uu___127_19856.nolabels);
                                           use_zfuel_name =
                                             (uu___127_19856.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___127_19856.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___127_19856.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____19798 with
                             | (env',e1,t_norm1) ->
                                 let uu____19866 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____19866 with
                                  | ((binders,body,uu____19887,t_body),curry)
                                      ->
                                      ((let uu____19899 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____19899
                                        then
                                          let uu____19900 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____19901 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____19900 uu____19901
                                        else ());
                                       (let uu____19903 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____19903 with
                                        | (vars,guards,env'1,binder_decls,uu____19930)
                                            ->
                                            let body1 =
                                              let uu____19944 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____19944
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
                                              let uu____19961 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____19961 curry fvb
                                                vars
                                               in
                                            let uu____19962 =
                                              let uu____19971 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____19971
                                              then
                                                let uu____19982 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____19983 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____19982, uu____19983)
                                              else
                                                (let uu____19993 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____19993))
                                               in
                                            (match uu____19962 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20016 =
                                                     let uu____20023 =
                                                       let uu____20024 =
                                                         let uu____20035 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____20035)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20024
                                                        in
                                                     let uu____20046 =
                                                       let uu____20049 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20049
                                                        in
                                                     (uu____20023,
                                                       uu____20046,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20016
                                                    in
                                                 let uu____20052 =
                                                   let uu____20055 =
                                                     let uu____20058 =
                                                       let uu____20061 =
                                                         let uu____20064 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____20064
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____20061
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20058
                                                      in
                                                   FStar_List.append decls1
                                                     uu____20055
                                                    in
                                                 (uu____20052, env2))))))
                        | uu____20069 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____20124 = varops.fresh "fuel"  in
                          (uu____20124, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____20127 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____20174  ->
                                  fun fvb  ->
                                    match uu____20174 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____20220 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____20220  in
                                        let gtok =
                                          let uu____20222 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____20222  in
                                        let env4 =
                                          let uu____20224 =
                                            let uu____20227 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_42  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_42) uu____20227
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____20224
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____20127 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____20327 t_norm
                              uu____20329 =
                              match (uu____20327, uu____20329) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____20359;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____20360;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____20362;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____20363;_})
                                  ->
                                  let uu____20384 =
                                    let uu____20391 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____20391 with
                                    | (tcenv',uu____20413,e_t) ->
                                        let uu____20419 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20430 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____20419 with
                                         | (e1,t_norm1) ->
                                             ((let uu___128_20446 = env3  in
                                               {
                                                 bindings =
                                                   (uu___128_20446.bindings);
                                                 depth =
                                                   (uu___128_20446.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___128_20446.warn);
                                                 cache =
                                                   (uu___128_20446.cache);
                                                 nolabels =
                                                   (uu___128_20446.nolabels);
                                                 use_zfuel_name =
                                                   (uu___128_20446.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___128_20446.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___128_20446.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____20384 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20461 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____20461
                                         then
                                           let uu____20462 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____20463 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____20464 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20462 uu____20463
                                             uu____20464
                                         else ());
                                        (let uu____20466 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____20466 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20503 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____20503
                                               then
                                                 let uu____20504 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____20505 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____20506 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____20507 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20504 uu____20505
                                                   uu____20506 uu____20507
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20511 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____20511 with
                                               | (vars,guards,env'1,binder_decls,uu____20542)
                                                   ->
                                                   let decl_g =
                                                     let uu____20556 =
                                                       let uu____20567 =
                                                         let uu____20570 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20570
                                                          in
                                                       (g, uu____20567,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20556
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
                                                     let uu____20595 =
                                                       let uu____20602 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____20602)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20595
                                                      in
                                                   let gsapp =
                                                     let uu____20612 =
                                                       let uu____20619 =
                                                         let uu____20622 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____20622 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20619)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20612
                                                      in
                                                   let gmax =
                                                     let uu____20628 =
                                                       let uu____20635 =
                                                         let uu____20638 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____20638 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20635)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20628
                                                      in
                                                   let body1 =
                                                     let uu____20644 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____20644
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____20646 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____20646 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____20664 =
                                                            let uu____20671 =
                                                              let uu____20672
                                                                =
                                                                let uu____20687
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
                                                                  uu____20687)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20672
                                                               in
                                                            let uu____20708 =
                                                              let uu____20711
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20711
                                                               in
                                                            (uu____20671,
                                                              uu____20708,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20664
                                                           in
                                                        let eqn_f =
                                                          let uu____20715 =
                                                            let uu____20722 =
                                                              let uu____20723
                                                                =
                                                                let uu____20734
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20734)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20723
                                                               in
                                                            (uu____20722,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20715
                                                           in
                                                        let eqn_g' =
                                                          let uu____20748 =
                                                            let uu____20755 =
                                                              let uu____20756
                                                                =
                                                                let uu____20767
                                                                  =
                                                                  let uu____20768
                                                                    =
                                                                    let uu____20773
                                                                    =
                                                                    let uu____20774
                                                                    =
                                                                    let uu____20781
                                                                    =
                                                                    let uu____20784
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____20784
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____20781)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20774
                                                                     in
                                                                    (gsapp,
                                                                    uu____20773)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____20768
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20767)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20756
                                                               in
                                                            (uu____20755,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20748
                                                           in
                                                        let uu____20807 =
                                                          let uu____20816 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____20816
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____20845)
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
                                                                  let uu____20870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____20870
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____20875
                                                                  =
                                                                  let uu____20882
                                                                    =
                                                                    let uu____20883
                                                                    =
                                                                    let uu____20894
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20894)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20883
                                                                     in
                                                                  (uu____20882,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____20875
                                                                 in
                                                              let uu____20915
                                                                =
                                                                let uu____20922
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____20922
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____20935
                                                                    =
                                                                    let uu____20938
                                                                    =
                                                                    let uu____20939
                                                                    =
                                                                    let uu____20946
                                                                    =
                                                                    let uu____20947
                                                                    =
                                                                    let uu____20958
                                                                    =
                                                                    let uu____20959
                                                                    =
                                                                    let uu____20964
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____20964,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____20959
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20958)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20947
                                                                     in
                                                                    (uu____20946,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20939
                                                                     in
                                                                    [uu____20938]
                                                                     in
                                                                    (d3,
                                                                    uu____20935)
                                                                 in
                                                              (match uu____20915
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
                                                        (match uu____20807
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
                            let uu____21029 =
                              let uu____21042 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21103  ->
                                   fun uu____21104  ->
                                     match (uu____21103, uu____21104) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21229 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21229 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21042
                               in
                            (match uu____21029 with
                             | (decls2,eqns,env01) ->
                                 let uu____21302 =
                                   let isDeclFun uu___94_21314 =
                                     match uu___94_21314 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21315 -> true
                                     | uu____21326 -> false  in
                                   let uu____21327 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____21327
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____21302 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____21367 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___95_21371  ->
                                 match uu___95_21371 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21372 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21378 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21378)))
                         in
                      if uu____21367
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
                   let uu____21430 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____21430
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
        let uu____21479 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____21479 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____21483 = encode_sigelt' env se  in
      match uu____21483 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21499 =
                  let uu____21500 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____21500  in
                [uu____21499]
            | uu____21501 ->
                let uu____21502 =
                  let uu____21505 =
                    let uu____21506 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21506  in
                  uu____21505 :: g  in
                let uu____21507 =
                  let uu____21510 =
                    let uu____21511 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21511  in
                  [uu____21510]  in
                FStar_List.append uu____21502 uu____21507
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
        let uu____21524 =
          let uu____21525 = FStar_Syntax_Subst.compress t  in
          uu____21525.FStar_Syntax_Syntax.n  in
        match uu____21524 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21529)) -> s = "opaque_to_smt"
        | uu____21530 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____21535 =
          let uu____21536 = FStar_Syntax_Subst.compress t  in
          uu____21536.FStar_Syntax_Syntax.n  in
        match uu____21535 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21540)) -> s = "uninterpreted_by_smt"
        | uu____21541 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21546 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____21551 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21562 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21565 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21568 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21583 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21587 =
            let uu____21588 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____21588 Prims.op_Negation  in
          if uu____21587
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____21614 ->
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
               let uu____21634 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____21634 with
               | (formals,uu____21652) ->
                   let arity = FStar_List.length formals  in
                   let uu____21670 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____21670 with
                    | (aname,atok,env2) ->
                        let uu____21690 =
                          let uu____21695 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____21695 env2  in
                        (match uu____21690 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____21707 =
                                 let uu____21708 =
                                   let uu____21719 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21735  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____21719,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____21708
                                  in
                               [uu____21707;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____21748 =
                               let aux uu____21800 uu____21801 =
                                 match (uu____21800, uu____21801) with
                                 | ((bv,uu____21853),(env3,acc_sorts,acc)) ->
                                     let uu____21891 = gen_term_var env3 bv
                                        in
                                     (match uu____21891 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____21748 with
                              | (uu____21963,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____21986 =
                                      let uu____21993 =
                                        let uu____21994 =
                                          let uu____22005 =
                                            let uu____22006 =
                                              let uu____22011 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____22011)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22006
                                             in
                                          ([[app]], xs_sorts, uu____22005)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____21994
                                         in
                                      (uu____21993,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____21986
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____22031 =
                                      let uu____22038 =
                                        let uu____22039 =
                                          let uu____22050 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____22050)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22039
                                         in
                                      (uu____22038,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22031
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____22069 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____22069 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22097,uu____22098)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22099 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____22099 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22116,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22122 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___96_22126  ->
                      match uu___96_22126 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22127 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22132 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22133 -> false))
               in
            Prims.op_Negation uu____22122  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22142 =
               let uu____22149 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22149 env fv t quals  in
             match uu____22142 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22164 =
                   let uu____22167 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22167  in
                 (uu____22164, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22175 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22175 with
           | (uu____22184,f1) ->
               let uu____22186 = encode_formula f1 env  in
               (match uu____22186 with
                | (f2,decls) ->
                    let g =
                      let uu____22200 =
                        let uu____22201 =
                          let uu____22208 =
                            let uu____22211 =
                              let uu____22212 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22212
                               in
                            FStar_Pervasives_Native.Some uu____22211  in
                          let uu____22213 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22208, uu____22213)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22201  in
                      [uu____22200]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22219) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22231 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22249 =
                       let uu____22252 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22252.FStar_Syntax_Syntax.fv_name  in
                     uu____22249.FStar_Syntax_Syntax.v  in
                   let uu____22253 =
                     let uu____22254 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22254  in
                   if uu____22253
                   then
                     let val_decl =
                       let uu___131_22282 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___131_22282.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___131_22282.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___131_22282.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____22287 = encode_sigelt' env1 val_decl  in
                     match uu____22287 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22231 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22315,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22317;
                          FStar_Syntax_Syntax.lbtyp = uu____22318;
                          FStar_Syntax_Syntax.lbeff = uu____22319;
                          FStar_Syntax_Syntax.lbdef = uu____22320;
                          FStar_Syntax_Syntax.lbattrs = uu____22321;
                          FStar_Syntax_Syntax.lbpos = uu____22322;_}::[]),uu____22323)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22346 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____22346 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____22375 =
                   let uu____22378 =
                     let uu____22379 =
                       let uu____22386 =
                         let uu____22387 =
                           let uu____22398 =
                             let uu____22399 =
                               let uu____22404 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____22404)  in
                             FStar_SMTEncoding_Util.mkEq uu____22399  in
                           ([[b2t_x]], [xx], uu____22398)  in
                         FStar_SMTEncoding_Util.mkForall uu____22387  in
                       (uu____22386,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____22379  in
                   [uu____22378]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22375
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22437,uu____22438) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_22447  ->
                  match uu___97_22447 with
                  | FStar_Syntax_Syntax.Discriminator uu____22448 -> true
                  | uu____22449 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22452,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22463 =
                     let uu____22464 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____22464.FStar_Ident.idText  in
                   uu____22463 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___98_22468  ->
                     match uu___98_22468 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22469 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22473) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___99_22490  ->
                  match uu___99_22490 with
                  | FStar_Syntax_Syntax.Projector uu____22491 -> true
                  | uu____22496 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____22499 = try_lookup_free_var env l  in
          (match uu____22499 with
           | FStar_Pervasives_Native.Some uu____22506 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___132_22510 = se  in
                 let uu____22511 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____22511;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___132_22510.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___132_22510.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___132_22510.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22518) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22536) ->
          let uu____22545 = encode_sigelts env ses  in
          (match uu____22545 with
           | (g,env1) ->
               let uu____22562 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___100_22585  ->
                         match uu___100_22585 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22586;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22587;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22588;_}
                             -> false
                         | uu____22591 -> true))
                  in
               (match uu____22562 with
                | (g',inversions) ->
                    let uu____22606 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___101_22627  ->
                              match uu___101_22627 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22628 ->
                                  true
                              | uu____22639 -> false))
                       in
                    (match uu____22606 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22657,tps,k,uu____22660,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___102_22677  ->
                    match uu___102_22677 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22678 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22687 = c  in
              match uu____22687 with
              | (name,args,uu____22692,uu____22693,uu____22694) ->
                  let uu____22699 =
                    let uu____22700 =
                      let uu____22711 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22728  ->
                                match uu____22728 with
                                | (uu____22735,sort,uu____22737) -> sort))
                         in
                      (name, uu____22711, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____22700  in
                  [uu____22699]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____22764 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____22770 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____22770 FStar_Option.isNone))
               in
            if uu____22764
            then []
            else
              (let uu____22802 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____22802 with
               | (xxsym,xx) ->
                   let uu____22811 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____22850  ->
                             fun l  ->
                               match uu____22850 with
                               | (out,decls) ->
                                   let uu____22870 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____22870 with
                                    | (uu____22881,data_t) ->
                                        let uu____22883 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____22883 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____22929 =
                                                 let uu____22930 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____22930.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____22929 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____22941,indices) ->
                                                   indices
                                               | uu____22963 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____22987  ->
                                                         match uu____22987
                                                         with
                                                         | (x,uu____22993) ->
                                                             let uu____22994
                                                               =
                                                               let uu____22995
                                                                 =
                                                                 let uu____23002
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23002,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____22995
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____22994)
                                                    env)
                                                in
                                             let uu____23005 =
                                               encode_args indices env1  in
                                             (match uu____23005 with
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
                                                      let uu____23031 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23047
                                                                 =
                                                                 let uu____23052
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23052,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23047)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23031
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23055 =
                                                      let uu____23056 =
                                                        let uu____23061 =
                                                          let uu____23062 =
                                                            let uu____23067 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23067,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23062
                                                           in
                                                        (out, uu____23061)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23056
                                                       in
                                                    (uu____23055,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____22811 with
                    | (data_ax,decls) ->
                        let uu____23080 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23080 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23091 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23091 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23095 =
                                 let uu____23102 =
                                   let uu____23103 =
                                     let uu____23114 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23129 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23114,
                                       uu____23129)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23103
                                    in
                                 let uu____23144 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23102,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23144)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23095
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23147 =
            let uu____23160 =
              let uu____23161 = FStar_Syntax_Subst.compress k  in
              uu____23161.FStar_Syntax_Syntax.n  in
            match uu____23160 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23206 -> (tps, k)  in
          (match uu____23147 with
           | (formals,res) ->
               let uu____23229 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23229 with
                | (formals1,res1) ->
                    let uu____23240 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23240 with
                     | (vars,guards,env',binder_decls,uu____23265) ->
                         let arity = FStar_List.length vars  in
                         let uu____23279 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____23279 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23302 =
                                  let uu____23309 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23309)  in
                                FStar_SMTEncoding_Util.mkApp uu____23302  in
                              let uu____23318 =
                                let tname_decl =
                                  let uu____23328 =
                                    let uu____23329 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23361  ->
                                              match uu____23361 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23374 = varops.next_id ()  in
                                    (tname, uu____23329,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23374, false)
                                     in
                                  constructor_or_logic_type_decl uu____23328
                                   in
                                let uu____23383 =
                                  match vars with
                                  | [] ->
                                      let uu____23396 =
                                        let uu____23397 =
                                          let uu____23400 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23400
                                           in
                                        push_free_var env1 t arity tname
                                          uu____23397
                                         in
                                      ([], uu____23396)
                                  | uu____23411 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____23420 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23420
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____23434 =
                                          let uu____23441 =
                                            let uu____23442 =
                                              let uu____23457 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23457)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23442
                                             in
                                          (uu____23441,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23434
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____23383 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23318 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23497 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____23497 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23515 =
                                               let uu____23516 =
                                                 let uu____23523 =
                                                   let uu____23524 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23524
                                                    in
                                                 (uu____23523,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23516
                                                in
                                             [uu____23515]
                                           else []  in
                                         let uu____23528 =
                                           let uu____23531 =
                                             let uu____23534 =
                                               let uu____23535 =
                                                 let uu____23542 =
                                                   let uu____23543 =
                                                     let uu____23554 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____23554)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23543
                                                    in
                                                 (uu____23542,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23535
                                                in
                                             [uu____23534]  in
                                           FStar_List.append karr uu____23531
                                            in
                                         FStar_List.append decls1 uu____23528
                                      in
                                   let aux =
                                     let uu____23570 =
                                       let uu____23573 =
                                         inversion_axioms tapp vars  in
                                       let uu____23576 =
                                         let uu____23579 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____23579]  in
                                       FStar_List.append uu____23573
                                         uu____23576
                                        in
                                     FStar_List.append kindingAx uu____23570
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23586,uu____23587,uu____23588,uu____23589,uu____23590)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23598,t,uu____23600,n_tps,uu____23602) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____23610 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____23610 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____23650 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____23650 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____23671 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____23671 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____23685 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____23685 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____23755 =
                                            mk_term_projector_name d x  in
                                          (uu____23755,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____23757 =
                                  let uu____23776 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23776, true)
                                   in
                                FStar_All.pipe_right uu____23757
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
                              let uu____23815 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____23815 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23827::uu____23828 ->
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
                                         let uu____23873 =
                                           let uu____23884 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____23884)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____23873
                                     | uu____23909 -> tok_typing  in
                                   let uu____23918 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____23918 with
                                    | (vars',guards',env'',decls_formals,uu____23943)
                                        ->
                                        let uu____23956 =
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
                                        (match uu____23956 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____23987 ->
                                                   let uu____23994 =
                                                     let uu____23995 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____23995
                                                      in
                                                   [uu____23994]
                                                in
                                             let encode_elim uu____24005 =
                                               let uu____24006 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24006 with
                                               | (head1,args) ->
                                                   let uu____24049 =
                                                     let uu____24050 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24050.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24049 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24060;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24061;_},uu____24062)
                                                        ->
                                                        let uu____24067 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24067
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24080
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24080
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
                                                                    uu____24123
                                                                    ->
                                                                    let uu____24124
                                                                    =
                                                                    let uu____24129
                                                                    =
                                                                    let uu____24130
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24130
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24129)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24124
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24146
                                                                    =
                                                                    let uu____24147
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24147
                                                                     in
                                                                    if
                                                                    uu____24146
                                                                    then
                                                                    let uu____24160
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24160]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24162
                                                                    =
                                                                    let uu____24175
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24225
                                                                     ->
                                                                    fun
                                                                    uu____24226
                                                                     ->
                                                                    match 
                                                                    (uu____24225,
                                                                    uu____24226)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24321
                                                                    =
                                                                    let uu____24328
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24328
                                                                     in
                                                                    (match uu____24321
                                                                    with
                                                                    | 
                                                                    (uu____24341,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24349
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24349
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24351
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24351
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
                                                                    uu____24175
                                                                     in
                                                                  (match uu____24162
                                                                   with
                                                                   | 
                                                                   (uu____24366,arg_vars,elim_eqns_or_guards,uu____24369)
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
                                                                    let uu____24397
                                                                    =
                                                                    let uu____24404
                                                                    =
                                                                    let uu____24405
                                                                    =
                                                                    let uu____24416
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24427
                                                                    =
                                                                    let uu____24428
                                                                    =
                                                                    let uu____24433
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24433)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24428
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24416,
                                                                    uu____24427)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24405
                                                                     in
                                                                    (uu____24404,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24397
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____24451
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____24451
                                                                    then
                                                                    let x =
                                                                    let uu____24457
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24457,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24459
                                                                    =
                                                                    let uu____24466
                                                                    =
                                                                    let uu____24467
                                                                    =
                                                                    let uu____24478
                                                                    =
                                                                    let uu____24483
                                                                    =
                                                                    let uu____24486
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____24486]
                                                                     in
                                                                    [uu____24483]
                                                                     in
                                                                    let uu____24491
                                                                    =
                                                                    let uu____24492
                                                                    =
                                                                    let uu____24497
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____24498
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____24497,
                                                                    uu____24498)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24492
                                                                     in
                                                                    (uu____24478,
                                                                    [x],
                                                                    uu____24491)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24467
                                                                     in
                                                                    let uu____24517
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24466,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24517)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24459
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24524
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
                                                                    (let uu____24552
                                                                    =
                                                                    let uu____24553
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24553
                                                                    dapp1  in
                                                                    [uu____24552])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24524
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____24560
                                                                    =
                                                                    let uu____24567
                                                                    =
                                                                    let uu____24568
                                                                    =
                                                                    let uu____24579
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24590
                                                                    =
                                                                    let uu____24591
                                                                    =
                                                                    let uu____24596
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____24596)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24591
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24579,
                                                                    uu____24590)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24568
                                                                     in
                                                                    (uu____24567,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24560)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____24616 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24616
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24629
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24629
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
                                                                    uu____24672
                                                                    ->
                                                                    let uu____24673
                                                                    =
                                                                    let uu____24678
                                                                    =
                                                                    let uu____24679
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24679
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24678)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24673
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24695
                                                                    =
                                                                    let uu____24696
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24696
                                                                     in
                                                                    if
                                                                    uu____24695
                                                                    then
                                                                    let uu____24709
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24709]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24711
                                                                    =
                                                                    let uu____24724
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24774
                                                                     ->
                                                                    fun
                                                                    uu____24775
                                                                     ->
                                                                    match 
                                                                    (uu____24774,
                                                                    uu____24775)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24870
                                                                    =
                                                                    let uu____24877
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24877
                                                                     in
                                                                    (match uu____24870
                                                                    with
                                                                    | 
                                                                    (uu____24890,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24898
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24898
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24900
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
                                                                    uu____24724
                                                                     in
                                                                  (match uu____24711
                                                                   with
                                                                   | 
                                                                   (uu____24915,arg_vars,elim_eqns_or_guards,uu____24918)
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
                                                                    let uu____24946
                                                                    =
                                                                    let uu____24953
                                                                    =
                                                                    let uu____24954
                                                                    =
                                                                    let uu____24965
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24976
                                                                    =
                                                                    let uu____24977
                                                                    =
                                                                    let uu____24982
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24982)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24977
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24965,
                                                                    uu____24976)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24954
                                                                     in
                                                                    (uu____24953,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24946
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____25000
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____25000
                                                                    then
                                                                    let x =
                                                                    let uu____25006
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25006,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25008
                                                                    =
                                                                    let uu____25015
                                                                    =
                                                                    let uu____25016
                                                                    =
                                                                    let uu____25027
                                                                    =
                                                                    let uu____25032
                                                                    =
                                                                    let uu____25035
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25035]
                                                                     in
                                                                    [uu____25032]
                                                                     in
                                                                    let uu____25040
                                                                    =
                                                                    let uu____25041
                                                                    =
                                                                    let uu____25046
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25047
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25046,
                                                                    uu____25047)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25041
                                                                     in
                                                                    (uu____25027,
                                                                    [x],
                                                                    uu____25040)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25016
                                                                     in
                                                                    let uu____25066
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25015,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25066)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25008
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25073
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
                                                                    (let uu____25101
                                                                    =
                                                                    let uu____25102
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25102
                                                                    dapp1  in
                                                                    [uu____25101])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25073
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25109
                                                                    =
                                                                    let uu____25116
                                                                    =
                                                                    let uu____25117
                                                                    =
                                                                    let uu____25128
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25139
                                                                    =
                                                                    let uu____25140
                                                                    =
                                                                    let uu____25145
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25145)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25140
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25128,
                                                                    uu____25139)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25117
                                                                     in
                                                                    (uu____25116,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25109)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____25164 ->
                                                        ((let uu____25166 =
                                                            let uu____25171 =
                                                              let uu____25172
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25173
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25172
                                                                uu____25173
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25171)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25166);
                                                         ([], [])))
                                                in
                                             let uu____25178 = encode_elim ()
                                                in
                                             (match uu____25178 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25198 =
                                                      let uu____25201 =
                                                        let uu____25204 =
                                                          let uu____25207 =
                                                            let uu____25210 =
                                                              let uu____25211
                                                                =
                                                                let uu____25222
                                                                  =
                                                                  let uu____25225
                                                                    =
                                                                    let uu____25226
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25226
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25225
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25222)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25211
                                                               in
                                                            [uu____25210]  in
                                                          let uu____25231 =
                                                            let uu____25234 =
                                                              let uu____25237
                                                                =
                                                                let uu____25240
                                                                  =
                                                                  let uu____25243
                                                                    =
                                                                    let uu____25246
                                                                    =
                                                                    let uu____25249
                                                                    =
                                                                    let uu____25250
                                                                    =
                                                                    let uu____25257
                                                                    =
                                                                    let uu____25258
                                                                    =
                                                                    let uu____25269
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25269)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25258
                                                                     in
                                                                    (uu____25257,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25250
                                                                     in
                                                                    let uu____25282
                                                                    =
                                                                    let uu____25285
                                                                    =
                                                                    let uu____25286
                                                                    =
                                                                    let uu____25293
                                                                    =
                                                                    let uu____25294
                                                                    =
                                                                    let uu____25305
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25316
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25305,
                                                                    uu____25316)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25294
                                                                     in
                                                                    (uu____25293,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25286
                                                                     in
                                                                    [uu____25285]
                                                                     in
                                                                    uu____25249
                                                                    ::
                                                                    uu____25282
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25246
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25243
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25240
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25237
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25234
                                                             in
                                                          FStar_List.append
                                                            uu____25207
                                                            uu____25231
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25204
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25201
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25198
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
           (fun uu____25362  ->
              fun se  ->
                match uu____25362 with
                | (g,env1) ->
                    let uu____25382 = encode_sigelt env1 se  in
                    (match uu____25382 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25439 =
        match uu____25439 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25471 ->
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
                 ((let uu____25477 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____25477
                   then
                     let uu____25478 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____25479 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____25480 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25478 uu____25479 uu____25480
                   else ());
                  (let uu____25482 = encode_term t1 env1  in
                   match uu____25482 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____25498 =
                         let uu____25505 =
                           let uu____25506 =
                             let uu____25507 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____25507
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____25506  in
                         new_term_constant_from_string env1 x uu____25505  in
                       (match uu____25498 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____25523 = FStar_Options.log_queries ()
                                 in
                              if uu____25523
                              then
                                let uu____25526 =
                                  let uu____25527 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____25528 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____25529 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25527 uu____25528 uu____25529
                                   in
                                FStar_Pervasives_Native.Some uu____25526
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25545,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____25559 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____25559 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25582,se,uu____25584) ->
                 let uu____25589 = encode_sigelt env1 se  in
                 (match uu____25589 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25606,se) ->
                 let uu____25612 = encode_sigelt env1 se  in
                 (match uu____25612 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____25629 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____25629 with | (uu____25652,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____25664 'Auu____25665 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____25664,'Auu____25665)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25733  ->
              match uu____25733 with
              | (l,uu____25745,uu____25746) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____25792  ->
              match uu____25792 with
              | (l,uu____25806,uu____25807) ->
                  let uu____25816 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____25817 =
                    let uu____25820 =
                      let uu____25821 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____25821  in
                    [uu____25820]  in
                  uu____25816 :: uu____25817))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____25846 =
      let uu____25849 =
        let uu____25850 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____25853 =
          let uu____25854 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____25854 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____25850;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____25853
        }  in
      [uu____25849]  in
    FStar_ST.op_Colon_Equals last_env uu____25846
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____25884 = FStar_ST.op_Bang last_env  in
      match uu____25884 with
      | [] -> failwith "No env; call init first!"
      | e::uu____25911 ->
          let uu___133_25914 = e  in
          let uu____25915 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___133_25914.bindings);
            depth = (uu___133_25914.depth);
            tcenv;
            warn = (uu___133_25914.warn);
            cache = (uu___133_25914.cache);
            nolabels = (uu___133_25914.nolabels);
            use_zfuel_name = (uu___133_25914.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_25914.encode_non_total_function_typ);
            current_module_name = uu____25915
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____25919 = FStar_ST.op_Bang last_env  in
    match uu____25919 with
    | [] -> failwith "Empty env stack"
    | uu____25945::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____25974  ->
    let uu____25975 = FStar_ST.op_Bang last_env  in
    match uu____25975 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___134_26009 = hd1  in
          {
            bindings = (uu___134_26009.bindings);
            depth = (uu___134_26009.depth);
            tcenv = (uu___134_26009.tcenv);
            warn = (uu___134_26009.warn);
            cache = refs;
            nolabels = (uu___134_26009.nolabels);
            use_zfuel_name = (uu___134_26009.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_26009.encode_non_total_function_typ);
            current_module_name = (uu___134_26009.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____26035  ->
    let uu____26036 = FStar_ST.op_Bang last_env  in
    match uu____26036 with
    | [] -> failwith "Popping an empty stack"
    | uu____26062::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> Prims.unit) =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let (pop : Prims.string -> Prims.unit) =
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
        | (uu____26126::uu____26127,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___135_26135 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___135_26135.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___135_26135.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___135_26135.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26136 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26151 =
        let uu____26154 =
          let uu____26155 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26155  in
        let uu____26156 = open_fact_db_tags env  in uu____26154 ::
          uu____26156
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26151
  
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
      let uu____26178 = encode_sigelt env se  in
      match uu____26178 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____26214 = FStar_Options.log_queries ()  in
        if uu____26214
        then
          let uu____26217 =
            let uu____26218 =
              let uu____26219 =
                let uu____26220 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26220 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26219  in
            FStar_SMTEncoding_Term.Caption uu____26218  in
          uu____26217 :: decls
        else decls  in
      (let uu____26231 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26231
       then
         let uu____26232 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26232
       else ());
      (let env =
         let uu____26235 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26235 tcenv  in
       let uu____26236 = encode_top_level_facts env se  in
       match uu____26236 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26250 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26250)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____26262 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26262
       then
         let uu____26263 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26263
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26298  ->
                 fun se  ->
                   match uu____26298 with
                   | (g,env2) ->
                       let uu____26318 = encode_top_level_facts env2 se  in
                       (match uu____26318 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26341 =
         encode_signature
           (let uu___136_26350 = env  in
            {
              bindings = (uu___136_26350.bindings);
              depth = (uu___136_26350.depth);
              tcenv = (uu___136_26350.tcenv);
              warn = false;
              cache = (uu___136_26350.cache);
              nolabels = (uu___136_26350.nolabels);
              use_zfuel_name = (uu___136_26350.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___136_26350.encode_non_total_function_typ);
              current_module_name = (uu___136_26350.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26341 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26367 = FStar_Options.log_queries ()  in
             if uu____26367
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___137_26375 = env1  in
               {
                 bindings = (uu___137_26375.bindings);
                 depth = (uu___137_26375.depth);
                 tcenv = (uu___137_26375.tcenv);
                 warn = true;
                 cache = (uu___137_26375.cache);
                 nolabels = (uu___137_26375.nolabels);
                 use_zfuel_name = (uu___137_26375.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___137_26375.encode_non_total_function_typ);
                 current_module_name = (uu___137_26375.current_module_name)
               });
            (let uu____26377 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____26377
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
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
        (let uu____26429 =
           let uu____26430 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____26430.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26429);
        (let env =
           let uu____26432 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____26432 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____26444 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26479 = aux rest  in
                 (match uu____26479 with
                  | (out,rest1) ->
                      let t =
                        let uu____26509 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____26509 with
                        | FStar_Pervasives_Native.Some uu____26514 ->
                            let uu____26515 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____26515
                              x.FStar_Syntax_Syntax.sort
                        | uu____26516 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____26520 =
                        let uu____26523 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___138_26526 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___138_26526.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___138_26526.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____26523 :: out  in
                      (uu____26520, rest1))
             | uu____26531 -> ([], bindings1)  in
           let uu____26538 = aux bindings  in
           match uu____26538 with
           | (closing,bindings1) ->
               let uu____26563 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____26563, bindings1)
            in
         match uu____26444 with
         | (q1,bindings1) ->
             let uu____26586 =
               let uu____26591 =
                 FStar_List.filter
                   (fun uu___103_26596  ->
                      match uu___103_26596 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26597 ->
                          false
                      | uu____26604 -> true) bindings1
                  in
               encode_env_bindings env uu____26591  in
             (match uu____26586 with
              | (env_decls,env1) ->
                  ((let uu____26622 =
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
                    if uu____26622
                    then
                      let uu____26623 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26623
                    else ());
                   (let uu____26625 = encode_formula q1 env1  in
                    match uu____26625 with
                    | (phi,qdecls) ->
                        let uu____26646 =
                          let uu____26651 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26651 phi
                           in
                        (match uu____26646 with
                         | (labels,phi1) ->
                             let uu____26668 = encode_labels labels  in
                             (match uu____26668 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____26705 =
                                      let uu____26712 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____26713 =
                                        varops.mk_unique "@query"  in
                                      (uu____26712,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26713)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26705
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
  