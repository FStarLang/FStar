open Prims
let add_fuel :
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives ()  in
      if uu____19 then tl1 else x :: tl1
  
let withenv :
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____30 ->
      ('Auu____29,'Auu____28) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____28,'Auu____30) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___79_107  ->
         match uu___79_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___102_143 = a  in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___102_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___102_143.FStar_Syntax_Syntax.sort)
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
        let fail uu____158 =
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
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail ())
  
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
    let uu___103_1621 = x  in
    let uu____1622 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1622;
      FStar_Syntax_Syntax.index = (uu___103_1621.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___103_1621.FStar_Syntax_Syntax.sort)
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
    'Auu____1771 ->
      ('Auu____1771,'Auu____1770 FStar_Pervasives_Native.option)
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
        fun t_decls  ->
          let names1 =
            FStar_All.pipe_right t_decls
              (FStar_List.collect
                 (fun uu___80_2101  ->
                    match uu___80_2101 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2105 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
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
           (fun uu___81_2124  ->
              match uu___81_2124 with
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
        (let uu___104_2193 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___104_2193.tcenv);
           warn = (uu___104_2193.warn);
           cache = (uu___104_2193.cache);
           nolabels = (uu___104_2193.nolabels);
           use_zfuel_name = (uu___104_2193.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___104_2193.encode_non_total_function_typ);
           current_module_name = (uu___104_2193.current_module_name)
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
        (let uu___105_2211 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___105_2211.depth);
           tcenv = (uu___105_2211.tcenv);
           warn = (uu___105_2211.warn);
           cache = (uu___105_2211.cache);
           nolabels = (uu___105_2211.nolabels);
           use_zfuel_name = (uu___105_2211.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___105_2211.encode_non_total_function_typ);
           current_module_name = (uu___105_2211.current_module_name)
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
          (let uu___106_2232 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___106_2232.depth);
             tcenv = (uu___106_2232.tcenv);
             warn = (uu___106_2232.warn);
             cache = (uu___106_2232.cache);
             nolabels = (uu___106_2232.nolabels);
             use_zfuel_name = (uu___106_2232.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___106_2232.encode_non_total_function_typ);
             current_module_name = (uu___106_2232.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___107_2242 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___107_2242.depth);
          tcenv = (uu___107_2242.tcenv);
          warn = (uu___107_2242.warn);
          cache = (uu___107_2242.cache);
          nolabels = (uu___107_2242.nolabels);
          use_zfuel_name = (uu___107_2242.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___107_2242.encode_non_total_function_typ);
          current_module_name = (uu___107_2242.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___82_2266  ->
             match uu___82_2266 with
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
          (let uu___108_2367 = env  in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___108_2367.depth);
             tcenv = (uu___108_2367.tcenv);
             warn = (uu___108_2367.warn);
             cache = (uu___108_2367.cache);
             nolabels = (uu___108_2367.nolabels);
             use_zfuel_name = (uu___108_2367.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___108_2367.encode_non_total_function_typ);
             current_module_name = (uu___108_2367.current_module_name)
           }))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___83_2378  ->
           match uu___83_2378 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2382 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2389 =
        lookup_binding env
          (fun uu___84_2394  ->
             match uu___84_2394 with
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
            let uu___109_2433 = env  in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___109_2433.depth);
              tcenv = (uu___109_2433.tcenv);
              warn = (uu___109_2433.warn);
              cache = (uu___109_2433.cache);
              nolabels = (uu___109_2433.nolabels);
              use_zfuel_name = (uu___109_2433.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___109_2433.encode_non_total_function_typ);
              current_module_name = (uu___109_2433.current_module_name)
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
        let uu___110_2461 = env  in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___110_2461.depth);
          tcenv = (uu___110_2461.tcenv);
          warn = (uu___110_2461.warn);
          cache = (uu___110_2461.cache);
          nolabels = (uu___110_2461.nolabels);
          use_zfuel_name = (uu___110_2461.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___110_2461.encode_non_total_function_typ);
          current_module_name = (uu___110_2461.current_module_name)
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
        (fun uu___85_2622  ->
           match uu___85_2622 with
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
               (fun uu___86_2930  ->
                  match uu___86_2930 with
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
  fun uu___87_3116  ->
    match uu___87_3116 with
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
                (fun a415  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a415)
                (fun a416  -> (Obj.magic binary) a416)
               in
            let sub1 =
              mk_l ()
                (fun a417  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a417)
                (fun a418  -> (Obj.magic binary) a418)
               in
            let minus =
              mk_l ()
                (fun a419  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a419)
                (fun a420  -> (Obj.magic unary) a420)
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
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
                  ((let uu____4859 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____4859);
                   t_decls)
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
                          (fun a421  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a421)
                          (fun a422  -> (Obj.magic binary) a422)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv ()
                          (fun a423  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a423)
                          (fun a424  -> (Obj.magic binary) a424)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv ()
                          (fun a425  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a425)
                          (fun a426  -> (Obj.magic binary) a426)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv ()
                          (fun a427  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a427)
                          (fun a428  -> (Obj.magic binary) a428)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv ()
                          (fun a429  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a429)
                          (fun a430  -> (Obj.magic binary) a430)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv ()
                          (fun a431  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a431)
                          (fun a432  -> (Obj.magic binary_arith) a432)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv ()
                          (fun a433  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a433)
                          (fun a434  -> (Obj.magic binary_arith) a434)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv ()
                          (fun a435  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a435)
                          (fun a436  -> (Obj.magic binary_arith) a436)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv ()
                          (fun a437  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a437)
                          (fun a438  -> (Obj.magic binary_arith) a438)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv ()
                          (fun a439  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a439)
                          (fun a440  -> (Obj.magic binary_arith) a440)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv ()
                          (fun a441  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a441)
                          (fun a442  -> (Obj.magic binary) a442)
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
                        mk_bv () (fun a443  -> (Obj.magic uu____5221) a443)
                          (fun a444  -> (Obj.magic unary) a444) uu____5226
                          arg_tms2
                         in
                      let to_int1 =
                        mk_bv ()
                          (fun a445  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a445) (fun a446  -> (Obj.magic unary) a446)
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv ()
                          (fun a447  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a447)
                          (fun a448  -> (Obj.magic unary_arith) a448)
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
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5585 =
             let uu____5586 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5586
              in
           failwith uu____5585
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____5593),uu____5594) ->
           let uu____5643 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____5651 -> false  in
           if uu____5643
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____5667;
              FStar_Syntax_Syntax.vars = uu____5668;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____5685 = varops.fresh "t"  in
             (uu____5685, FStar_SMTEncoding_Term.Term_sort)  in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym  in
           let decl =
             let uu____5688 =
               let uu____5699 =
                 let uu____5702 = FStar_Util.format1 "alien term (%s)" desc
                    in
                 FStar_Pervasives_Native.Some uu____5702  in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____5699)
                in
             FStar_SMTEncoding_Term.DeclFun uu____5688  in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5710) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5720 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____5720, [])
       | FStar_Syntax_Syntax.Tm_type uu____5723 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5727) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____5752 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5752 with
            | (binders1,res) ->
                let uu____5763 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5763
                then
                  let uu____5768 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5768 with
                   | (vars,guards,env',decls,uu____5793) ->
                       let fsym =
                         let uu____5811 = varops.fresh "f"  in
                         (uu____5811, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5814 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___111_5823 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___111_5823.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___111_5823.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___111_5823.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___111_5823.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___111_5823.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___111_5823.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___111_5823.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___111_5823.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___111_5823.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___111_5823.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___111_5823.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___111_5823.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___111_5823.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___111_5823.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___111_5823.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___111_5823.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___111_5823.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___111_5823.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___111_5823.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___111_5823.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___111_5823.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___111_5823.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___111_5823.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___111_5823.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___111_5823.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___111_5823.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___111_5823.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___111_5823.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___111_5823.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___111_5823.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___111_5823.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___111_5823.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___111_5823.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___111_5823.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____5814 with
                        | (pre_opt,res_t) ->
                            let uu____5834 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5834 with
                             | (res_pred,decls') ->
                                 let uu____5845 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5858 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____5858, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5862 =
                                         encode_formula pre env'  in
                                       (match uu____5862 with
                                        | (guard,decls0) ->
                                            let uu____5875 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____5875, decls0))
                                    in
                                 (match uu____5845 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____5887 =
                                          let uu____5898 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____5898)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5887
                                         in
                                      let cvars =
                                        let uu____5916 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____5916
                                          (FStar_List.filter
                                             (fun uu____5930  ->
                                                match uu____5930 with
                                                | (x,uu____5936) ->
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
                                      let uu____5955 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____5955 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5963 =
                                             let uu____5964 =
                                               let uu____5971 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5971)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5964
                                              in
                                           (uu____5963,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____5991 =
                                               let uu____5992 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____5992
                                                in
                                             varops.mk_unique uu____5991  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6003 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6003
                                             then
                                               let uu____6006 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6006
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
                                             let uu____6014 =
                                               let uu____6021 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6021)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6014
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
                                             let uu____6033 =
                                               let uu____6040 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6040,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6033
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
                                             let uu____6061 =
                                               let uu____6068 =
                                                 let uu____6069 =
                                                   let uu____6080 =
                                                     let uu____6081 =
                                                       let uu____6086 =
                                                         let uu____6087 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6087
                                                          in
                                                       (f_has_t, uu____6086)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6081
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6080)
                                                    in
                                                 mkForall_fuel uu____6069  in
                                               (uu____6068,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6061
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6110 =
                                               let uu____6117 =
                                                 let uu____6118 =
                                                   let uu____6129 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6129)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6118
                                                  in
                                               (uu____6117,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6110
                                              in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____6154 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6154);
                                            (t1, t_decls)))))))
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
                     let uu____6169 =
                       let uu____6176 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6176,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6169  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6188 =
                       let uu____6195 =
                         let uu____6196 =
                           let uu____6207 =
                             let uu____6208 =
                               let uu____6213 =
                                 let uu____6214 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6214
                                  in
                               (f_has_t, uu____6213)  in
                             FStar_SMTEncoding_Util.mkImp uu____6208  in
                           ([[f_has_t]], [fsym], uu____6207)  in
                         mkForall_fuel uu____6196  in
                       (uu____6195, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6188  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6241 ->
           let uu____6248 =
             let uu____6253 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6253 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6260;
                 FStar_Syntax_Syntax.vars = uu____6261;_} ->
                 let uu____6268 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6268 with
                  | (b,f1) ->
                      let uu____6293 =
                        let uu____6294 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6294  in
                      (uu____6293, f1))
             | uu____6303 -> failwith "impossible"  in
           (match uu____6248 with
            | (x,f) ->
                let uu____6314 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6314 with
                 | (base_t,decls) ->
                     let uu____6325 = gen_term_var env x  in
                     (match uu____6325 with
                      | (x1,xtm,env') ->
                          let uu____6339 = encode_formula f env'  in
                          (match uu____6339 with
                           | (refinement,decls') ->
                               let uu____6350 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6350 with
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
                                      let uu____6366 =
                                        let uu____6369 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6376 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6369
                                          uu____6376
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6366
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6409  ->
                                              match uu____6409 with
                                              | (y,uu____6415) ->
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
                                    let uu____6448 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6448 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6456 =
                                           let uu____6457 =
                                             let uu____6464 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6464)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6457
                                            in
                                         (uu____6456,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6485 =
                                             let uu____6486 =
                                               let uu____6487 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6487
                                                in
                                             Prims.strcat module_name
                                               uu____6486
                                              in
                                           varops.mk_unique uu____6485  in
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
                                           let uu____6501 =
                                             let uu____6508 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6508)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6501
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
                                           let uu____6523 =
                                             let uu____6530 =
                                               let uu____6531 =
                                                 let uu____6542 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6542)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6531
                                                in
                                             (uu____6530,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6523
                                            in
                                         let t_kinding =
                                           let uu____6560 =
                                             let uu____6567 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6567,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6560
                                            in
                                         let t_interp =
                                           let uu____6585 =
                                             let uu____6592 =
                                               let uu____6593 =
                                                 let uu____6604 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6604)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6593
                                                in
                                             let uu____6627 =
                                               let uu____6630 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6630
                                                in
                                             (uu____6592, uu____6627,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6585
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____6637 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6637);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6667 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6667  in
           let uu____6668 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____6668 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6680 =
                    let uu____6687 =
                      let uu____6688 =
                        let uu____6689 =
                          let uu____6690 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6690
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____6689  in
                      varops.mk_unique uu____6688  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6687)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6680  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6695 ->
           let uu____6710 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6710 with
            | (head1,args_e) ->
                let uu____6751 =
                  let uu____6764 =
                    let uu____6765 = FStar_Syntax_Subst.compress head1  in
                    uu____6765.FStar_Syntax_Syntax.n  in
                  (uu____6764, args_e)  in
                (match uu____6751 with
                 | uu____6780 when head_redex env head1 ->
                     let uu____6793 = whnf env t  in
                     encode_term uu____6793 env
                 | uu____6794 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6813 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6827;
                       FStar_Syntax_Syntax.vars = uu____6828;_},uu____6829),uu____6830::
                    (v1,uu____6832)::(v2,uu____6834)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6885 = encode_term v1 env  in
                     (match uu____6885 with
                      | (v11,decls1) ->
                          let uu____6896 = encode_term v2 env  in
                          (match uu____6896 with
                           | (v21,decls2) ->
                               let uu____6907 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6907,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6911::(v1,uu____6913)::(v2,uu____6915)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6962 = encode_term v1 env  in
                     (match uu____6962 with
                      | (v11,decls1) ->
                          let uu____6973 = encode_term v2 env  in
                          (match uu____6973 with
                           | (v21,decls2) ->
                               let uu____6984 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6984,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6988)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7014)::(rng,uu____7016)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7051) ->
                     let e0 =
                       let uu____7069 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7069
                        in
                     ((let uu____7077 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7077
                       then
                         let uu____7078 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7078
                       else ());
                      (let e =
                         let uu____7083 =
                           let uu____7084 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7085 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7084
                             uu____7085
                            in
                         uu____7083 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7094),(arg,uu____7096)::[]) -> encode_term arg env
                 | uu____7121 ->
                     let uu____7134 = encode_args args_e env  in
                     (match uu____7134 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7189 = encode_term head1 env  in
                            match uu____7189 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7253 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7253 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7331  ->
                                                 fun uu____7332  ->
                                                   match (uu____7331,
                                                           uu____7332)
                                                   with
                                                   | ((bv,uu____7354),
                                                      (a,uu____7356)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7374 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7374
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7379 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7379 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7394 =
                                                   let uu____7401 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7410 =
                                                     let uu____7411 =
                                                       let uu____7412 =
                                                         let uu____7413 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7413
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7412
                                                        in
                                                     varops.mk_unique
                                                       uu____7411
                                                      in
                                                   (uu____7401,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7410)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7394
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7430 = lookup_free_var_sym env fv  in
                            match uu____7430 with
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
                                   FStar_Syntax_Syntax.pos = uu____7462;
                                   FStar_Syntax_Syntax.vars = uu____7463;_},uu____7464)
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
                                   FStar_Syntax_Syntax.pos = uu____7475;
                                   FStar_Syntax_Syntax.vars = uu____7476;_},uu____7477)
                                ->
                                let uu____7482 =
                                  let uu____7483 =
                                    let uu____7488 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7488
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7483
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7482
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7518 =
                                  let uu____7519 =
                                    let uu____7524 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7524
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7519
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7518
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7553,(FStar_Util.Inl t1,uu____7555),uu____7556)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7605,(FStar_Util.Inr c,uu____7607),uu____7608)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7657 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7684 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7684
                                  in
                               let uu____7685 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7685 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7701;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7702;_},uu____7703)
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
                                     | uu____7717 ->
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
           let uu____7766 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7766 with
            | (bs1,body1,opening) ->
                let fallback uu____7789 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7796 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7796, [decl])  in
                let is_impure rc =
                  let uu____7803 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7803 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7813 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____7813
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____7833 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7833
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____7837 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7837)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7844 =
                         let uu____7849 =
                           let uu____7850 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7850
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7849)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7844);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7852 =
                       (is_impure rc) &&
                         (let uu____7854 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____7854)
                        in
                     if uu____7852
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____7861 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7861 with
                        | (vars,guards,envbody,decls,uu____7886) ->
                            let body2 =
                              let uu____7900 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____7900
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____7902 = encode_term body2 envbody  in
                            (match uu____7902 with
                             | (body3,decls') ->
                                 let uu____7913 =
                                   let uu____7922 = codomain_eff rc  in
                                   match uu____7922 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7941 = encode_term tfun env
                                          in
                                       (match uu____7941 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7913 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7973 =
                                          let uu____7984 =
                                            let uu____7985 =
                                              let uu____7990 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7990, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7985
                                             in
                                          ([], vars, uu____7984)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____7973
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
                                            let uu____8002 =
                                              let uu____8005 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8005
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8002
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8024 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8024 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8032 =
                                             let uu____8033 =
                                               let uu____8040 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8040)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8033
                                              in
                                           (uu____8032,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8051 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8051 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8062 =
                                                    let uu____8063 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8063 = cache_size
                                                     in
                                                  if uu____8062
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
                                                    let uu____8079 =
                                                      let uu____8080 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8080
                                                       in
                                                    varops.mk_unique
                                                      uu____8079
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
                                                  let uu____8087 =
                                                    let uu____8094 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8094)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8087
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
                                                      let uu____8112 =
                                                        let uu____8113 =
                                                          let uu____8120 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8120,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8113
                                                         in
                                                      [uu____8112]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8133 =
                                                    let uu____8140 =
                                                      let uu____8141 =
                                                        let uu____8152 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8152)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8141
                                                       in
                                                    (uu____8140,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8133
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
                                                ((let uu____8169 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8169);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8172,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8173;
                          FStar_Syntax_Syntax.lbunivs = uu____8174;
                          FStar_Syntax_Syntax.lbtyp = uu____8175;
                          FStar_Syntax_Syntax.lbeff = uu____8176;
                          FStar_Syntax_Syntax.lbdef = uu____8177;
                          FStar_Syntax_Syntax.lbattrs = uu____8178;_}::uu____8179),uu____8180)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8210;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8212;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8214;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8238 ->
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
              let uu____8308 =
                let uu____8313 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8313 env  in
              match uu____8308 with
              | (ee1,decls1) ->
                  let uu____8334 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8334 with
                   | (xs,e21) ->
                       let uu____8359 = FStar_List.hd xs  in
                       (match uu____8359 with
                        | (x1,uu____8373) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8375 = encode_body e21 env'  in
                            (match uu____8375 with
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
            let uu____8407 =
              let uu____8414 =
                let uu____8415 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8415  in
              gen_term_var env uu____8414  in
            match uu____8407 with
            | (scrsym,scr',env1) ->
                let uu____8423 = encode_term e env1  in
                (match uu____8423 with
                 | (scr,decls) ->
                     let uu____8434 =
                       let encode_branch b uu____8459 =
                         match uu____8459 with
                         | (else_case,decls1) ->
                             let uu____8478 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8478 with
                              | (p,w,br) ->
                                  let uu____8504 = encode_pat env1 p  in
                                  (match uu____8504 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8541  ->
                                                   match uu____8541 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8548 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8570 =
                                               encode_term w1 env2  in
                                             (match uu____8570 with
                                              | (w2,decls2) ->
                                                  let uu____8583 =
                                                    let uu____8584 =
                                                      let uu____8589 =
                                                        let uu____8590 =
                                                          let uu____8595 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8595)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8590
                                                         in
                                                      (guard, uu____8589)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8584
                                                     in
                                                  (uu____8583, decls2))
                                          in
                                       (match uu____8548 with
                                        | (guard1,decls2) ->
                                            let uu____8608 =
                                              encode_br br env2  in
                                            (match uu____8608 with
                                             | (br1,decls3) ->
                                                 let uu____8621 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8621,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8434 with
                      | (match_tm,decls1) ->
                          let uu____8640 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8640, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____8680 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____8680
       then
         let uu____8681 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8681
       else ());
      (let uu____8683 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8683 with
       | (vars,pat_term) ->
           let uu____8700 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8753  ->
                     fun v1  ->
                       match uu____8753 with
                       | (env1,vars1) ->
                           let uu____8805 = gen_term_var env1 v1  in
                           (match uu____8805 with
                            | (xx,uu____8827,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8700 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8906 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8907 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8908 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8916 = encode_const c env1  in
                      (match uu____8916 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8930::uu____8931 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8934 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8957 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____8957 with
                        | (uu____8964,uu____8965::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8968 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9001  ->
                                  match uu____9001 with
                                  | (arg,uu____9009) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9015 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9015))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9042) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9073 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9096 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9140  ->
                                  match uu____9140 with
                                  | (arg,uu____9154) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9160 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9160))
                         in
                      FStar_All.pipe_right uu____9096 FStar_List.flatten
                   in
                let pat_term1 uu____9188 = encode_term pat_term env1  in
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
      let uu____9198 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9236  ->
                fun uu____9237  ->
                  match (uu____9236, uu____9237) with
                  | ((tms,decls),(t,uu____9273)) ->
                      let uu____9294 = encode_term t env  in
                      (match uu____9294 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9198 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9351 = FStar_Syntax_Util.list_elements e  in
        match uu____9351 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9372 =
          let uu____9387 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9387 FStar_Syntax_Util.head_and_args  in
        match uu____9372 with
        | (head1,args) ->
            let uu____9426 =
              let uu____9439 =
                let uu____9440 = FStar_Syntax_Util.un_uinst head1  in
                uu____9440.FStar_Syntax_Syntax.n  in
              (uu____9439, args)  in
            (match uu____9426 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9454,uu____9455)::(e,uu____9457)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9492 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9528 =
            let uu____9543 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9543 FStar_Syntax_Util.head_and_args
             in
          match uu____9528 with
          | (head1,args) ->
              let uu____9584 =
                let uu____9597 =
                  let uu____9598 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9598.FStar_Syntax_Syntax.n  in
                (uu____9597, args)  in
              (match uu____9584 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9615)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9642 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9664 = smt_pat_or1 t1  in
            (match uu____9664 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9680 = list_elements1 e  in
                 FStar_All.pipe_right uu____9680
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9698 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9698
                           (FStar_List.map one_pat)))
             | uu____9709 ->
                 let uu____9714 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9714])
        | uu____9735 ->
            let uu____9738 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9738]
         in
      let uu____9759 =
        let uu____9778 =
          let uu____9779 = FStar_Syntax_Subst.compress t  in
          uu____9779.FStar_Syntax_Syntax.n  in
        match uu____9778 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9818 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9818 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9861;
                        FStar_Syntax_Syntax.effect_name = uu____9862;
                        FStar_Syntax_Syntax.result_typ = uu____9863;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9865)::(post,uu____9867)::(pats,uu____9869)::[];
                        FStar_Syntax_Syntax.flags = uu____9870;_}
                      ->
                      let uu____9911 = lemma_pats pats  in
                      (binders1, pre, post, uu____9911)
                  | uu____9928 -> failwith "impos"))
        | uu____9947 -> failwith "Impos"  in
      match uu____9759 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___112_9995 = env  in
            {
              bindings = (uu___112_9995.bindings);
              depth = (uu___112_9995.depth);
              tcenv = (uu___112_9995.tcenv);
              warn = (uu___112_9995.warn);
              cache = (uu___112_9995.cache);
              nolabels = (uu___112_9995.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___112_9995.encode_non_total_function_typ);
              current_module_name = (uu___112_9995.current_module_name)
            }  in
          let uu____9996 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9996 with
           | (vars,guards,env2,decls,uu____10021) ->
               let uu____10034 =
                 let uu____10049 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10103 =
                             let uu____10114 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10114
                               FStar_List.unzip
                              in
                           match uu____10103 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10049 FStar_List.unzip  in
               (match uu____10034 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___113_10266 = env2  in
                      {
                        bindings = (uu___113_10266.bindings);
                        depth = (uu___113_10266.depth);
                        tcenv = (uu___113_10266.tcenv);
                        warn = (uu___113_10266.warn);
                        cache = (uu___113_10266.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___113_10266.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___113_10266.encode_non_total_function_typ);
                        current_module_name =
                          (uu___113_10266.current_module_name)
                      }  in
                    let uu____10267 =
                      let uu____10272 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10272 env3  in
                    (match uu____10267 with
                     | (pre1,decls'') ->
                         let uu____10279 =
                           let uu____10284 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10284 env3  in
                         (match uu____10279 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10294 =
                                let uu____10295 =
                                  let uu____10306 =
                                    let uu____10307 =
                                      let uu____10312 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10312, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10307
                                     in
                                  (pats, vars, uu____10306)  in
                                FStar_SMTEncoding_Util.mkForall uu____10295
                                 in
                              (uu____10294, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____10325 = FStar_Syntax_Util.head_and_args t  in
      match uu____10325 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10384::(x,uu____10386)::(t1,uu____10388)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10435 = encode_term x env  in
               (match uu____10435 with
                | (x1,decls) ->
                    let uu____10448 = encode_term t1 env  in
                    (match uu____10448 with
                     | (t2,decls') ->
                         let uu____10461 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10461, (FStar_List.append decls decls'))))
           | uu____10464 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10487 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10487
        then
          let uu____10488 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10489 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10488 uu____10489
        else ()  in
      let enc f r l =
        let uu____10522 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10550 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10550 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10522 with
        | (decls,args) ->
            let uu____10579 =
              let uu___114_10580 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10580.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10580.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10579, decls)
         in
      let const_op f r uu____10611 =
        let uu____10624 = f r  in (uu____10624, [])  in
      let un_op f l =
        let uu____10643 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10643  in
      let bin_op f uu___88_10659 =
        match uu___88_10659 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10670 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10704 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10727  ->
                 match uu____10727 with
                 | (t,uu____10741) ->
                     let uu____10742 = encode_formula t env  in
                     (match uu____10742 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10704 with
        | (decls,phis) ->
            let uu____10771 =
              let uu___115_10772 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___115_10772.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___115_10772.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10771, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10833  ->
               match uu____10833 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10852) -> false
                    | uu____10853 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10868 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10868
        else
          (let uu____10882 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10882 r rf)
         in
      let mk_imp1 r uu___89_10907 =
        match uu___89_10907 with
        | (lhs,uu____10913)::(rhs,uu____10915)::[] ->
            let uu____10942 = encode_formula rhs env  in
            (match uu____10942 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10957) ->
                      (l1, decls1)
                  | uu____10962 ->
                      let uu____10963 = encode_formula lhs env  in
                      (match uu____10963 with
                       | (l2,decls2) ->
                           let uu____10974 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10974, (FStar_List.append decls1 decls2)))))
        | uu____10977 -> failwith "impossible"  in
      let mk_ite r uu___90_10998 =
        match uu___90_10998 with
        | (guard,uu____11004)::(_then,uu____11006)::(_else,uu____11008)::[]
            ->
            let uu____11045 = encode_formula guard env  in
            (match uu____11045 with
             | (g,decls1) ->
                 let uu____11056 = encode_formula _then env  in
                 (match uu____11056 with
                  | (t,decls2) ->
                      let uu____11067 = encode_formula _else env  in
                      (match uu____11067 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11081 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11106 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11106  in
      let connectives =
        let uu____11124 =
          let uu____11137 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11137)  in
        let uu____11154 =
          let uu____11169 =
            let uu____11182 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11182)  in
          let uu____11199 =
            let uu____11214 =
              let uu____11229 =
                let uu____11242 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11242)  in
              let uu____11259 =
                let uu____11274 =
                  let uu____11289 =
                    let uu____11302 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11302)  in
                  [uu____11289;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11274  in
              uu____11229 :: uu____11259  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11214  in
          uu____11169 :: uu____11199  in
        uu____11124 :: uu____11154  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11623 = encode_formula phi' env  in
            (match uu____11623 with
             | (phi2,decls) ->
                 let uu____11634 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11634, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11635 ->
            let uu____11642 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11642 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11681 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11681 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11693;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11695;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11697;_}::[]),e2)
            ->
            let uu____11721 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11721 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11768::(x,uu____11770)::(t,uu____11772)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11819 = encode_term x env  in
                 (match uu____11819 with
                  | (x1,decls) ->
                      let uu____11830 = encode_term t env  in
                      (match uu____11830 with
                       | (t1,decls') ->
                           let uu____11841 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11841, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11846)::(msg,uu____11848)::(phi2,uu____11850)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11895 =
                   let uu____11900 =
                     let uu____11901 = FStar_Syntax_Subst.compress r  in
                     uu____11901.FStar_Syntax_Syntax.n  in
                   let uu____11904 =
                     let uu____11905 = FStar_Syntax_Subst.compress msg  in
                     uu____11905.FStar_Syntax_Syntax.n  in
                   (uu____11900, uu____11904)  in
                 (match uu____11895 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11914))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11920 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11927)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11952 when head_redex env head2 ->
                 let uu____11965 = whnf env phi1  in
                 encode_formula uu____11965 env
             | uu____11966 ->
                 let uu____11979 = encode_term phi1 env  in
                 (match uu____11979 with
                  | (tt,decls) ->
                      let uu____11990 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___116_11993 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___116_11993.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___116_11993.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____11990, decls)))
        | uu____11994 ->
            let uu____11995 = encode_term phi1 env  in
            (match uu____11995 with
             | (tt,decls) ->
                 let uu____12006 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___117_12009 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___117_12009.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___117_12009.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12006, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12045 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12045 with
        | (vars,guards,env2,decls,uu____12084) ->
            let uu____12097 =
              let uu____12110 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12162 =
                          let uu____12173 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12213  ->
                                    match uu____12213 with
                                    | (t,uu____12227) ->
                                        encode_smt_pattern t
                                          (let uu___118_12233 = env2  in
                                           {
                                             bindings =
                                               (uu___118_12233.bindings);
                                             depth = (uu___118_12233.depth);
                                             tcenv = (uu___118_12233.tcenv);
                                             warn = (uu___118_12233.warn);
                                             cache = (uu___118_12233.cache);
                                             nolabels =
                                               (uu___118_12233.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___118_12233.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___118_12233.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12173 FStar_List.unzip
                           in
                        match uu____12162 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12110 FStar_List.unzip  in
            (match uu____12097 with
             | (pats,decls') ->
                 let uu____12342 = encode_formula body env2  in
                 (match uu____12342 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12374;
                             FStar_SMTEncoding_Term.rng = uu____12375;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12390 -> guards  in
                      let uu____12395 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12395, body1,
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
                (fun uu____12455  ->
                   match uu____12455 with
                   | (x,uu____12461) ->
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
               let uu____12469 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12481 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12481) uu____12469 tl1
                in
             let uu____12484 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12511  ->
                       match uu____12511 with
                       | (b,uu____12517) ->
                           let uu____12518 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12518))
                in
             (match uu____12484 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12524) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12538 =
                    let uu____12543 =
                      let uu____12544 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12544
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12543)
                     in
                  FStar_Errors.log_issue pos uu____12538)
          in
       let uu____12545 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12545 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12554 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12612  ->
                     match uu____12612 with
                     | (l,uu____12626) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12554 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12659,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12699 = encode_q_body env vars pats body  in
             match uu____12699 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12744 =
                     let uu____12755 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12755)  in
                   FStar_SMTEncoding_Term.mkForall uu____12744
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12774 = encode_q_body env vars pats body  in
             match uu____12774 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12818 =
                   let uu____12819 =
                     let uu____12830 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12830)  in
                   FStar_SMTEncoding_Term.mkExists uu____12819
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____12818, decls))))

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
  let uu____12933 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____12933 with
  | (asym,a) ->
      let uu____12940 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____12940 with
       | (xsym,x) ->
           let uu____12947 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____12947 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____12995 =
                      let uu____13006 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13006, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12995  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13032 =
                      let uu____13039 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13039)  in
                    FStar_SMTEncoding_Util.mkApp uu____13032  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13052 =
                    let uu____13055 =
                      let uu____13058 =
                        let uu____13061 =
                          let uu____13062 =
                            let uu____13069 =
                              let uu____13070 =
                                let uu____13081 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13081)  in
                              FStar_SMTEncoding_Util.mkForall uu____13070  in
                            (uu____13069, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13062  in
                        let uu____13098 =
                          let uu____13101 =
                            let uu____13102 =
                              let uu____13109 =
                                let uu____13110 =
                                  let uu____13121 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13121)  in
                                FStar_SMTEncoding_Util.mkForall uu____13110
                                 in
                              (uu____13109,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13102  in
                          [uu____13101]  in
                        uu____13061 :: uu____13098  in
                      xtok_decl :: uu____13058  in
                    xname_decl :: uu____13055  in
                  (xtok1, (FStar_List.length vars), uu____13052)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13218 =
                    let uu____13233 =
                      let uu____13244 =
                        let uu____13245 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13245
                         in
                      quant axy uu____13244  in
                    (FStar_Parser_Const.op_Eq, uu____13233)  in
                  let uu____13256 =
                    let uu____13273 =
                      let uu____13288 =
                        let uu____13299 =
                          let uu____13300 =
                            let uu____13301 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13301  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13300
                           in
                        quant axy uu____13299  in
                      (FStar_Parser_Const.op_notEq, uu____13288)  in
                    let uu____13312 =
                      let uu____13329 =
                        let uu____13344 =
                          let uu____13355 =
                            let uu____13356 =
                              let uu____13357 =
                                let uu____13362 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13363 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13362, uu____13363)  in
                              FStar_SMTEncoding_Util.mkLT uu____13357  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13356
                             in
                          quant xy uu____13355  in
                        (FStar_Parser_Const.op_LT, uu____13344)  in
                      let uu____13374 =
                        let uu____13391 =
                          let uu____13406 =
                            let uu____13417 =
                              let uu____13418 =
                                let uu____13419 =
                                  let uu____13424 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13425 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13424, uu____13425)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13419  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13418
                               in
                            quant xy uu____13417  in
                          (FStar_Parser_Const.op_LTE, uu____13406)  in
                        let uu____13436 =
                          let uu____13453 =
                            let uu____13468 =
                              let uu____13479 =
                                let uu____13480 =
                                  let uu____13481 =
                                    let uu____13486 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13487 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13486, uu____13487)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13481  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13480
                                 in
                              quant xy uu____13479  in
                            (FStar_Parser_Const.op_GT, uu____13468)  in
                          let uu____13498 =
                            let uu____13515 =
                              let uu____13530 =
                                let uu____13541 =
                                  let uu____13542 =
                                    let uu____13543 =
                                      let uu____13548 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13549 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13548, uu____13549)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13543
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13542
                                   in
                                quant xy uu____13541  in
                              (FStar_Parser_Const.op_GTE, uu____13530)  in
                            let uu____13560 =
                              let uu____13577 =
                                let uu____13592 =
                                  let uu____13603 =
                                    let uu____13604 =
                                      let uu____13605 =
                                        let uu____13610 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13611 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13610, uu____13611)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13605
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13604
                                     in
                                  quant xy uu____13603  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13592)
                                 in
                              let uu____13622 =
                                let uu____13639 =
                                  let uu____13654 =
                                    let uu____13665 =
                                      let uu____13666 =
                                        let uu____13667 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13667
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13666
                                       in
                                    quant qx uu____13665  in
                                  (FStar_Parser_Const.op_Minus, uu____13654)
                                   in
                                let uu____13678 =
                                  let uu____13695 =
                                    let uu____13710 =
                                      let uu____13721 =
                                        let uu____13722 =
                                          let uu____13723 =
                                            let uu____13728 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____13729 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____13728, uu____13729)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13723
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13722
                                         in
                                      quant xy uu____13721  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13710)
                                     in
                                  let uu____13740 =
                                    let uu____13757 =
                                      let uu____13772 =
                                        let uu____13783 =
                                          let uu____13784 =
                                            let uu____13785 =
                                              let uu____13790 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____13791 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____13790, uu____13791)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13785
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13784
                                           in
                                        quant xy uu____13783  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13772)
                                       in
                                    let uu____13802 =
                                      let uu____13819 =
                                        let uu____13834 =
                                          let uu____13845 =
                                            let uu____13846 =
                                              let uu____13847 =
                                                let uu____13852 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____13853 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____13852, uu____13853)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13847
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13846
                                             in
                                          quant xy uu____13845  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13834)
                                         in
                                      let uu____13864 =
                                        let uu____13881 =
                                          let uu____13896 =
                                            let uu____13907 =
                                              let uu____13908 =
                                                let uu____13909 =
                                                  let uu____13914 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____13915 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____13914, uu____13915)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13909
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13908
                                               in
                                            quant xy uu____13907  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13896)
                                           in
                                        let uu____13926 =
                                          let uu____13943 =
                                            let uu____13958 =
                                              let uu____13969 =
                                                let uu____13970 =
                                                  let uu____13971 =
                                                    let uu____13976 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____13977 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____13976,
                                                      uu____13977)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13971
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13970
                                                 in
                                              quant xy uu____13969  in
                                            (FStar_Parser_Const.op_And,
                                              uu____13958)
                                             in
                                          let uu____13988 =
                                            let uu____14005 =
                                              let uu____14020 =
                                                let uu____14031 =
                                                  let uu____14032 =
                                                    let uu____14033 =
                                                      let uu____14038 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14039 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14038,
                                                        uu____14039)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14033
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14032
                                                   in
                                                quant xy uu____14031  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14020)
                                               in
                                            let uu____14050 =
                                              let uu____14067 =
                                                let uu____14082 =
                                                  let uu____14093 =
                                                    let uu____14094 =
                                                      let uu____14095 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14095
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14094
                                                     in
                                                  quant qx uu____14093  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14082)
                                                 in
                                              [uu____14067]  in
                                            uu____14005 :: uu____14050  in
                                          uu____13943 :: uu____13988  in
                                        uu____13881 :: uu____13926  in
                                      uu____13819 :: uu____13864  in
                                    uu____13757 :: uu____13802  in
                                  uu____13695 :: uu____13740  in
                                uu____13639 :: uu____13678  in
                              uu____13577 :: uu____13622  in
                            uu____13515 :: uu____13560  in
                          uu____13453 :: uu____13498  in
                        uu____13391 :: uu____13436  in
                      uu____13329 :: uu____13374  in
                    uu____13273 :: uu____13312  in
                  uu____13218 :: uu____13256  in
                let mk1 l v1 =
                  let uu____14345 =
                    let uu____14356 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14422  ->
                              match uu____14422 with
                              | (l',uu____14438) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14356
                      (FStar_Option.map
                         (fun uu____14510  ->
                            match uu____14510 with | (uu____14533,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14345 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14618  ->
                          match uu____14618 with
                          | (l',uu____14634) -> FStar_Ident.lid_equals l l'))
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
        let uu____14676 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14676 with
        | (xxsym,xx) ->
            let uu____14683 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14683 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14693 =
                   let uu____14700 =
                     let uu____14701 =
                       let uu____14712 =
                         let uu____14713 =
                           let uu____14718 =
                             let uu____14719 =
                               let uu____14724 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14724)  in
                             FStar_SMTEncoding_Util.mkEq uu____14719  in
                           (xx_has_type, uu____14718)  in
                         FStar_SMTEncoding_Util.mkImp uu____14713  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14712)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14701  in
                   let uu____14749 =
                     let uu____14750 =
                       let uu____14751 =
                         let uu____14752 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14752  in
                       Prims.strcat module_name uu____14751  in
                     varops.mk_unique uu____14750  in
                   (uu____14700, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14749)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14693)
  
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
    let uu____14788 =
      let uu____14789 =
        let uu____14796 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14796, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14789  in
    let uu____14799 =
      let uu____14802 =
        let uu____14803 =
          let uu____14810 =
            let uu____14811 =
              let uu____14822 =
                let uu____14823 =
                  let uu____14828 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____14828)  in
                FStar_SMTEncoding_Util.mkImp uu____14823  in
              ([[typing_pred]], [xx], uu____14822)  in
            mkForall_fuel uu____14811  in
          (uu____14810, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14803  in
      [uu____14802]  in
    uu____14788 :: uu____14799  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____14870 =
      let uu____14871 =
        let uu____14878 =
          let uu____14879 =
            let uu____14890 =
              let uu____14895 =
                let uu____14898 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____14898]  in
              [uu____14895]  in
            let uu____14903 =
              let uu____14904 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14904 tt  in
            (uu____14890, [bb], uu____14903)  in
          FStar_SMTEncoding_Util.mkForall uu____14879  in
        (uu____14878, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14871  in
    let uu____14925 =
      let uu____14928 =
        let uu____14929 =
          let uu____14936 =
            let uu____14937 =
              let uu____14948 =
                let uu____14949 =
                  let uu____14954 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____14954)  in
                FStar_SMTEncoding_Util.mkImp uu____14949  in
              ([[typing_pred]], [xx], uu____14948)  in
            mkForall_fuel uu____14937  in
          (uu____14936, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14929  in
      [uu____14928]  in
    uu____14870 :: uu____14925  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15004 =
        let uu____15005 =
          let uu____15012 =
            let uu____15015 =
              let uu____15018 =
                let uu____15021 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15022 =
                  let uu____15025 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15025]  in
                uu____15021 :: uu____15022  in
              tt :: uu____15018  in
            tt :: uu____15015  in
          ("Prims.Precedes", uu____15012)  in
        FStar_SMTEncoding_Util.mkApp uu____15005  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15004  in
    let precedes_y_x =
      let uu____15029 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15029  in
    let uu____15032 =
      let uu____15033 =
        let uu____15040 =
          let uu____15041 =
            let uu____15052 =
              let uu____15057 =
                let uu____15060 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15060]  in
              [uu____15057]  in
            let uu____15065 =
              let uu____15066 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15066 tt  in
            (uu____15052, [bb], uu____15065)  in
          FStar_SMTEncoding_Util.mkForall uu____15041  in
        (uu____15040, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15033  in
    let uu____15087 =
      let uu____15090 =
        let uu____15091 =
          let uu____15098 =
            let uu____15099 =
              let uu____15110 =
                let uu____15111 =
                  let uu____15116 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15116)  in
                FStar_SMTEncoding_Util.mkImp uu____15111  in
              ([[typing_pred]], [xx], uu____15110)  in
            mkForall_fuel uu____15099  in
          (uu____15098, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15091  in
      let uu____15141 =
        let uu____15144 =
          let uu____15145 =
            let uu____15152 =
              let uu____15153 =
                let uu____15164 =
                  let uu____15165 =
                    let uu____15170 =
                      let uu____15171 =
                        let uu____15174 =
                          let uu____15177 =
                            let uu____15180 =
                              let uu____15181 =
                                let uu____15186 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15187 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15186, uu____15187)  in
                              FStar_SMTEncoding_Util.mkGT uu____15181  in
                            let uu____15188 =
                              let uu____15191 =
                                let uu____15192 =
                                  let uu____15197 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15198 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15197, uu____15198)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15192  in
                              let uu____15199 =
                                let uu____15202 =
                                  let uu____15203 =
                                    let uu____15208 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15209 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15208, uu____15209)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15203  in
                                [uu____15202]  in
                              uu____15191 :: uu____15199  in
                            uu____15180 :: uu____15188  in
                          typing_pred_y :: uu____15177  in
                        typing_pred :: uu____15174  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15171  in
                    (uu____15170, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15165  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15164)
                 in
              mkForall_fuel uu____15153  in
            (uu____15152,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15145  in
        [uu____15144]  in
      uu____15090 :: uu____15141  in
    uu____15032 :: uu____15087  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15255 =
      let uu____15256 =
        let uu____15263 =
          let uu____15264 =
            let uu____15275 =
              let uu____15280 =
                let uu____15283 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15283]  in
              [uu____15280]  in
            let uu____15288 =
              let uu____15289 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15289 tt  in
            (uu____15275, [bb], uu____15288)  in
          FStar_SMTEncoding_Util.mkForall uu____15264  in
        (uu____15263, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15256  in
    let uu____15310 =
      let uu____15313 =
        let uu____15314 =
          let uu____15321 =
            let uu____15322 =
              let uu____15333 =
                let uu____15334 =
                  let uu____15339 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15339)  in
                FStar_SMTEncoding_Util.mkImp uu____15334  in
              ([[typing_pred]], [xx], uu____15333)  in
            mkForall_fuel uu____15322  in
          (uu____15321, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15314  in
      [uu____15313]  in
    uu____15255 :: uu____15310  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15392 =
      let uu____15393 =
        let uu____15400 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15400, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15393  in
    [uu____15392]  in
  let mk_and_interp env conj uu____15412 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15437 =
      let uu____15438 =
        let uu____15445 =
          let uu____15446 =
            let uu____15457 =
              let uu____15458 =
                let uu____15463 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15463, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15458  in
            ([[l_and_a_b]], [aa; bb], uu____15457)  in
          FStar_SMTEncoding_Util.mkForall uu____15446  in
        (uu____15445, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15438  in
    [uu____15437]  in
  let mk_or_interp env disj uu____15501 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15526 =
      let uu____15527 =
        let uu____15534 =
          let uu____15535 =
            let uu____15546 =
              let uu____15547 =
                let uu____15552 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15552, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15547  in
            ([[l_or_a_b]], [aa; bb], uu____15546)  in
          FStar_SMTEncoding_Util.mkForall uu____15535  in
        (uu____15534, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15527  in
    [uu____15526]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15615 =
      let uu____15616 =
        let uu____15623 =
          let uu____15624 =
            let uu____15635 =
              let uu____15636 =
                let uu____15641 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15641, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15636  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15635)  in
          FStar_SMTEncoding_Util.mkForall uu____15624  in
        (uu____15623, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15616  in
    [uu____15615]  in
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
    let uu____15714 =
      let uu____15715 =
        let uu____15722 =
          let uu____15723 =
            let uu____15734 =
              let uu____15735 =
                let uu____15740 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15740, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15735  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15734)  in
          FStar_SMTEncoding_Util.mkForall uu____15723  in
        (uu____15722, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15715  in
    [uu____15714]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15811 =
      let uu____15812 =
        let uu____15819 =
          let uu____15820 =
            let uu____15831 =
              let uu____15832 =
                let uu____15837 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____15837, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15832  in
            ([[l_imp_a_b]], [aa; bb], uu____15831)  in
          FStar_SMTEncoding_Util.mkForall uu____15820  in
        (uu____15819, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15812  in
    [uu____15811]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15900 =
      let uu____15901 =
        let uu____15908 =
          let uu____15909 =
            let uu____15920 =
              let uu____15921 =
                let uu____15926 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____15926, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15921  in
            ([[l_iff_a_b]], [aa; bb], uu____15920)  in
          FStar_SMTEncoding_Util.mkForall uu____15909  in
        (uu____15908, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15901  in
    [uu____15900]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____15978 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15978  in
    let uu____15981 =
      let uu____15982 =
        let uu____15989 =
          let uu____15990 =
            let uu____16001 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16001)  in
          FStar_SMTEncoding_Util.mkForall uu____15990  in
        (uu____15989, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15982  in
    [uu____15981]  in
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
      let uu____16061 =
        let uu____16068 =
          let uu____16071 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16071]  in
        ("Valid", uu____16068)  in
      FStar_SMTEncoding_Util.mkApp uu____16061  in
    let uu____16074 =
      let uu____16075 =
        let uu____16082 =
          let uu____16083 =
            let uu____16094 =
              let uu____16095 =
                let uu____16100 =
                  let uu____16101 =
                    let uu____16112 =
                      let uu____16117 =
                        let uu____16120 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16120]  in
                      [uu____16117]  in
                    let uu____16125 =
                      let uu____16126 =
                        let uu____16131 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16131, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16126  in
                    (uu____16112, [xx1], uu____16125)  in
                  FStar_SMTEncoding_Util.mkForall uu____16101  in
                (uu____16100, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16095  in
            ([[l_forall_a_b]], [aa; bb], uu____16094)  in
          FStar_SMTEncoding_Util.mkForall uu____16083  in
        (uu____16082, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16075  in
    [uu____16074]  in
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
      let uu____16213 =
        let uu____16220 =
          let uu____16223 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16223]  in
        ("Valid", uu____16220)  in
      FStar_SMTEncoding_Util.mkApp uu____16213  in
    let uu____16226 =
      let uu____16227 =
        let uu____16234 =
          let uu____16235 =
            let uu____16246 =
              let uu____16247 =
                let uu____16252 =
                  let uu____16253 =
                    let uu____16264 =
                      let uu____16269 =
                        let uu____16272 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16272]  in
                      [uu____16269]  in
                    let uu____16277 =
                      let uu____16278 =
                        let uu____16283 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16283, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16278  in
                    (uu____16264, [xx1], uu____16277)  in
                  FStar_SMTEncoding_Util.mkExists uu____16253  in
                (uu____16252, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16247  in
            ([[l_exists_a_b]], [aa; bb], uu____16246)  in
          FStar_SMTEncoding_Util.mkForall uu____16235  in
        (uu____16234, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16227  in
    [uu____16226]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16343 =
      let uu____16344 =
        let uu____16351 =
          let uu____16352 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16352 range_ty  in
        let uu____16353 = varops.mk_unique "typing_range_const"  in
        (uu____16351, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16353)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16344  in
    [uu____16343]  in
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
        let uu____16387 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16387 x1 t  in
      let uu____16388 =
        let uu____16399 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16399)  in
      FStar_SMTEncoding_Util.mkForall uu____16388  in
    let uu____16422 =
      let uu____16423 =
        let uu____16430 =
          let uu____16431 =
            let uu____16442 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16442)  in
          FStar_SMTEncoding_Util.mkForall uu____16431  in
        (uu____16430,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16423  in
    [uu____16422]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____16492 =
      let uu____16493 =
        let uu____16500 =
          let uu____16501 =
            let uu____16516 =
              let uu____16517 =
                let uu____16522 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____16523 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____16522, uu____16523)  in
              FStar_SMTEncoding_Util.mkAnd uu____16517  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16516)
             in
          FStar_SMTEncoding_Util.mkForall' uu____16501  in
        (uu____16500,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16493  in
    [uu____16492]  in
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
          let uu____16869 =
            FStar_Util.find_opt
              (fun uu____16895  ->
                 match uu____16895 with
                 | (l,uu____16907) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16869 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16932,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16968 = encode_function_type_as_formula t env  in
        match uu____16968 with
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
              let uu____17008 =
                ((let uu____17011 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____17011) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____17008
              then
                let arg_sorts =
                  let uu____17021 =
                    let uu____17022 = FStar_Syntax_Subst.compress t_norm  in
                    uu____17022.FStar_Syntax_Syntax.n  in
                  match uu____17021 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17028) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____17058  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____17063 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____17065 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____17065 with
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
                (let uu____17098 = prims.is lid  in
                 if uu____17098
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17106 = prims.mk lid vname  in
                   match uu____17106 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17133 =
                      let uu____17144 = curried_arrow_formals_comp t_norm  in
                      match uu____17144 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17162 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17162
                            then
                              let uu____17163 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___119_17166 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___119_17166.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___119_17166.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___119_17166.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___119_17166.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___119_17166.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___119_17166.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___119_17166.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___119_17166.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___119_17166.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___119_17166.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___119_17166.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___119_17166.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___119_17166.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___119_17166.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___119_17166.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___119_17166.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___119_17166.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___119_17166.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___119_17166.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___119_17166.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___119_17166.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___119_17166.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___119_17166.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___119_17166.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___119_17166.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___119_17166.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___119_17166.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___119_17166.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___119_17166.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___119_17166.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___119_17166.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___119_17166.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___119_17166.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___119_17166.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17163
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17178 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17178)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17133 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____17228 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____17228 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17253 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___91_17295  ->
                                       match uu___91_17295 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17299 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17299 with
                                            | (uu____17320,(xxsym,uu____17322))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17340 =
                                                  let uu____17341 =
                                                    let uu____17348 =
                                                      let uu____17349 =
                                                        let uu____17360 =
                                                          let uu____17361 =
                                                            let uu____17366 =
                                                              let uu____17367
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17367
                                                               in
                                                            (vapp,
                                                              uu____17366)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17361
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17360)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17349
                                                       in
                                                    (uu____17348,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17341
                                                   in
                                                [uu____17340])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17386 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17386 with
                                            | (uu____17407,(xxsym,uu____17409))
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
                                                let uu____17432 =
                                                  let uu____17433 =
                                                    let uu____17440 =
                                                      let uu____17441 =
                                                        let uu____17452 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17452)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17441
                                                       in
                                                    (uu____17440,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17433
                                                   in
                                                [uu____17432])
                                       | uu____17469 -> []))
                                in
                             let uu____17470 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17470 with
                              | (vars,guards,env',decls1,uu____17497) ->
                                  let uu____17510 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17519 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17519, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17521 =
                                          encode_formula p env'  in
                                        (match uu____17521 with
                                         | (g,ds) ->
                                             let uu____17532 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17532,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17510 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17545 =
                                           let uu____17552 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17552)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17545
                                          in
                                       let uu____17561 =
                                         let vname_decl =
                                           let uu____17569 =
                                             let uu____17580 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17590  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17580,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17569
                                            in
                                         let uu____17599 =
                                           let env2 =
                                             let uu___120_17605 = env1  in
                                             {
                                               bindings =
                                                 (uu___120_17605.bindings);
                                               depth = (uu___120_17605.depth);
                                               tcenv = (uu___120_17605.tcenv);
                                               warn = (uu___120_17605.warn);
                                               cache = (uu___120_17605.cache);
                                               nolabels =
                                                 (uu___120_17605.nolabels);
                                               use_zfuel_name =
                                                 (uu___120_17605.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___120_17605.current_module_name)
                                             }  in
                                           let uu____17606 =
                                             let uu____17607 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17607
                                              in
                                           if uu____17606
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17599 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17622::uu____17623 ->
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
                                                     let uu____17663 =
                                                       let uu____17674 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17674)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17663
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17701 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17704 =
                                               match formals with
                                               | [] ->
                                                   let uu____17721 =
                                                     let uu____17722 =
                                                       let uu____17725 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17725
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____17722
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17721)
                                               | uu____17734 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17741 =
                                                       let uu____17748 =
                                                         let uu____17749 =
                                                           let uu____17760 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17760)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17749
                                                          in
                                                       (uu____17748,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17741
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17704 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17561 with
                                        | (decls2,env2) ->
                                            let uu____17803 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17811 =
                                                encode_term res_t1 env'  in
                                              match uu____17811 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17824 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17824, decls)
                                               in
                                            (match uu____17803 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17835 =
                                                     let uu____17842 =
                                                       let uu____17843 =
                                                         let uu____17854 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17854)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17843
                                                        in
                                                     (uu____17842,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17835
                                                    in
                                                 let freshness =
                                                   let uu____17870 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17870
                                                   then
                                                     let uu____17875 =
                                                       let uu____17876 =
                                                         let uu____17887 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17898 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17887,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17898)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17876
                                                        in
                                                     let uu____17901 =
                                                       let uu____17904 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17904]  in
                                                     uu____17875 ::
                                                       uu____17901
                                                   else []  in
                                                 let g =
                                                   let uu____17909 =
                                                     let uu____17912 =
                                                       let uu____17915 =
                                                         let uu____17918 =
                                                           let uu____17921 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17921
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17918
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17915
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17912
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17909
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
          let uu____17946 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____17946 with
          | FStar_Pervasives_Native.None  ->
              let uu____17957 = encode_free_var false env x t t_norm []  in
              (match uu____17957 with
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
            let uu____18010 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____18010 with
            | (decls,env1) ->
                let uu____18029 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18029
                then
                  let uu____18036 =
                    let uu____18039 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18039  in
                  (uu____18036, env1)
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
             (fun uu____18091  ->
                fun lb  ->
                  match uu____18091 with
                  | (decls,env1) ->
                      let uu____18111 =
                        let uu____18118 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18118
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18111 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18139 = FStar_Syntax_Util.head_and_args t  in
    match uu____18139 with
    | (hd1,args) ->
        let uu____18176 =
          let uu____18177 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18177.FStar_Syntax_Syntax.n  in
        (match uu____18176 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18181,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18200 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18222  ->
      fun quals  ->
        match uu____18222 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18298 = FStar_Util.first_N nbinders formals  in
              match uu____18298 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18379  ->
                         fun uu____18380  ->
                           match (uu____18379, uu____18380) with
                           | ((formal,uu____18398),(binder,uu____18400)) ->
                               let uu____18409 =
                                 let uu____18416 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18416)  in
                               FStar_Syntax_Syntax.NT uu____18409) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18424 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18455  ->
                              match uu____18455 with
                              | (x,i) ->
                                  let uu____18466 =
                                    let uu___121_18467 = x  in
                                    let uu____18468 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_18467.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_18467.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18468
                                    }  in
                                  (uu____18466, i)))
                       in
                    FStar_All.pipe_right uu____18424
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18486 =
                      let uu____18487 = FStar_Syntax_Subst.compress body  in
                      let uu____18488 =
                        let uu____18489 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18489
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18487
                        uu____18488
                       in
                    uu____18486 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18550 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18550
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___122_18553 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_18553.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_18553.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_18553.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_18553.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_18553.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_18553.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_18553.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_18553.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_18553.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_18553.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_18553.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_18553.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_18553.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_18553.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_18553.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_18553.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_18553.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_18553.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_18553.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___122_18553.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___122_18553.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___122_18553.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_18553.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_18553.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___122_18553.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_18553.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_18553.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___122_18553.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___122_18553.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_18553.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___122_18553.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___122_18553.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___122_18553.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___122_18553.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18586 = FStar_Syntax_Util.abs_formals e  in
                match uu____18586 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18650::uu____18651 ->
                         let uu____18666 =
                           let uu____18667 =
                             let uu____18670 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18670
                              in
                           uu____18667.FStar_Syntax_Syntax.n  in
                         (match uu____18666 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18713 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18713 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18755 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18755
                                   then
                                     let uu____18790 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18790 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18884  ->
                                                   fun uu____18885  ->
                                                     match (uu____18884,
                                                             uu____18885)
                                                     with
                                                     | ((x,uu____18903),
                                                        (b,uu____18905)) ->
                                                         let uu____18914 =
                                                           let uu____18921 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____18921)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18914)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____18923 =
                                            let uu____18944 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____18944)
                                             in
                                          (uu____18923, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19012 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19012 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19101) ->
                              let uu____19106 =
                                let uu____19127 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19127  in
                              (uu____19106, true)
                          | uu____19192 when Prims.op_Negation norm1 ->
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
                          | uu____19194 ->
                              let uu____19195 =
                                let uu____19196 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19197 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19196
                                  uu____19197
                                 in
                              failwith uu____19195)
                     | uu____19222 ->
                         let rec aux' t_norm2 =
                           let uu____19247 =
                             let uu____19248 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19248.FStar_Syntax_Syntax.n  in
                           match uu____19247 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19289 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19289 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19317 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19317 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19397)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19402 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19458 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19458
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19470 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19533  ->
                            fun lb  ->
                              match uu____19533 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19588 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19588
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19591 =
                                      let uu____19600 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19600
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19591 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19470 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____19715 =
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
                        | uu____19721 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19729 = mk_fv ()  in
                                   mk_Apply uu____19729 vars)
                            else
                              (let uu____19731 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____19731)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19783;
                             FStar_Syntax_Syntax.lbeff = uu____19784;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____19786;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____19810 =
                              let uu____19817 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____19817 with
                              | (tcenv',uu____19835,e_t) ->
                                  let uu____19841 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19852 -> failwith "Impossible"
                                     in
                                  (match uu____19841 with
                                   | (e1,t_norm1) ->
                                       ((let uu___125_19868 = env2  in
                                         {
                                           bindings =
                                             (uu___125_19868.bindings);
                                           depth = (uu___125_19868.depth);
                                           tcenv = tcenv';
                                           warn = (uu___125_19868.warn);
                                           cache = (uu___125_19868.cache);
                                           nolabels =
                                             (uu___125_19868.nolabels);
                                           use_zfuel_name =
                                             (uu___125_19868.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___125_19868.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___125_19868.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____19810 with
                             | (env',e1,t_norm1) ->
                                 let uu____19878 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____19878 with
                                  | ((binders,body,uu____19899,t_body),curry)
                                      ->
                                      ((let uu____19911 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____19911
                                        then
                                          let uu____19912 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____19913 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____19912 uu____19913
                                        else ());
                                       (let uu____19915 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____19915 with
                                        | (vars,guards,env'1,binder_decls,uu____19942)
                                            ->
                                            let body1 =
                                              let uu____19956 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____19956
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
                                              let uu____19973 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____19973 curry fvb
                                                vars
                                               in
                                            let uu____19974 =
                                              let uu____19983 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____19983
                                              then
                                                let uu____19994 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____19995 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____19994, uu____19995)
                                              else
                                                (let uu____20005 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____20005))
                                               in
                                            (match uu____19974 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20028 =
                                                     let uu____20035 =
                                                       let uu____20036 =
                                                         let uu____20047 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____20047)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20036
                                                        in
                                                     let uu____20058 =
                                                       let uu____20061 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20061
                                                        in
                                                     (uu____20035,
                                                       uu____20058,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20028
                                                    in
                                                 let uu____20064 =
                                                   let uu____20067 =
                                                     let uu____20070 =
                                                       let uu____20073 =
                                                         let uu____20076 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____20076
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____20073
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20070
                                                      in
                                                   FStar_List.append decls1
                                                     uu____20067
                                                    in
                                                 (uu____20064, env2))))))
                        | uu____20081 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____20136 = varops.fresh "fuel"  in
                          (uu____20136, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____20139 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____20186  ->
                                  fun fvb  ->
                                    match uu____20186 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____20232 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____20232  in
                                        let gtok =
                                          let uu____20234 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____20234  in
                                        let env4 =
                                          let uu____20236 =
                                            let uu____20239 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_42  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_42) uu____20239
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____20236
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____20139 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____20339 t_norm
                              uu____20341 =
                              match (uu____20339, uu____20341) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____20371;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____20372;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____20374;_})
                                  ->
                                  let uu____20395 =
                                    let uu____20402 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____20402 with
                                    | (tcenv',uu____20424,e_t) ->
                                        let uu____20430 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20441 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____20430 with
                                         | (e1,t_norm1) ->
                                             ((let uu___126_20457 = env3  in
                                               {
                                                 bindings =
                                                   (uu___126_20457.bindings);
                                                 depth =
                                                   (uu___126_20457.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___126_20457.warn);
                                                 cache =
                                                   (uu___126_20457.cache);
                                                 nolabels =
                                                   (uu___126_20457.nolabels);
                                                 use_zfuel_name =
                                                   (uu___126_20457.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___126_20457.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___126_20457.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____20395 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20472 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____20472
                                         then
                                           let uu____20473 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____20474 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____20475 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20473 uu____20474
                                             uu____20475
                                         else ());
                                        (let uu____20477 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____20477 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20514 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____20514
                                               then
                                                 let uu____20515 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____20516 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____20517 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____20518 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20515 uu____20516
                                                   uu____20517 uu____20518
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20522 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____20522 with
                                               | (vars,guards,env'1,binder_decls,uu____20553)
                                                   ->
                                                   let decl_g =
                                                     let uu____20567 =
                                                       let uu____20578 =
                                                         let uu____20581 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20581
                                                          in
                                                       (g, uu____20578,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20567
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
                                                     let uu____20606 =
                                                       let uu____20613 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____20613)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20606
                                                      in
                                                   let gsapp =
                                                     let uu____20623 =
                                                       let uu____20630 =
                                                         let uu____20633 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____20633 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20630)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20623
                                                      in
                                                   let gmax =
                                                     let uu____20639 =
                                                       let uu____20646 =
                                                         let uu____20649 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____20649 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20646)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20639
                                                      in
                                                   let body1 =
                                                     let uu____20655 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____20655
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____20657 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____20657 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____20675 =
                                                            let uu____20682 =
                                                              let uu____20683
                                                                =
                                                                let uu____20698
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
                                                                  uu____20698)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20683
                                                               in
                                                            let uu____20719 =
                                                              let uu____20722
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20722
                                                               in
                                                            (uu____20682,
                                                              uu____20719,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20675
                                                           in
                                                        let eqn_f =
                                                          let uu____20726 =
                                                            let uu____20733 =
                                                              let uu____20734
                                                                =
                                                                let uu____20745
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20745)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20734
                                                               in
                                                            (uu____20733,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20726
                                                           in
                                                        let eqn_g' =
                                                          let uu____20759 =
                                                            let uu____20766 =
                                                              let uu____20767
                                                                =
                                                                let uu____20778
                                                                  =
                                                                  let uu____20779
                                                                    =
                                                                    let uu____20784
                                                                    =
                                                                    let uu____20785
                                                                    =
                                                                    let uu____20792
                                                                    =
                                                                    let uu____20795
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____20795
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____20792)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20785
                                                                     in
                                                                    (gsapp,
                                                                    uu____20784)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____20779
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20778)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20767
                                                               in
                                                            (uu____20766,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20759
                                                           in
                                                        let uu____20818 =
                                                          let uu____20827 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____20827
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____20856)
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
                                                                  let uu____20881
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____20881
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____20886
                                                                  =
                                                                  let uu____20893
                                                                    =
                                                                    let uu____20894
                                                                    =
                                                                    let uu____20905
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20905)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20894
                                                                     in
                                                                  (uu____20893,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____20886
                                                                 in
                                                              let uu____20926
                                                                =
                                                                let uu____20933
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____20933
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____20946
                                                                    =
                                                                    let uu____20949
                                                                    =
                                                                    let uu____20950
                                                                    =
                                                                    let uu____20957
                                                                    =
                                                                    let uu____20958
                                                                    =
                                                                    let uu____20969
                                                                    =
                                                                    let uu____20970
                                                                    =
                                                                    let uu____20975
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____20975,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____20970
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20969)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20958
                                                                     in
                                                                    (uu____20957,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20950
                                                                     in
                                                                    [uu____20949]
                                                                     in
                                                                    (d3,
                                                                    uu____20946)
                                                                 in
                                                              (match uu____20926
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
                                                        (match uu____20818
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
                            let uu____21040 =
                              let uu____21053 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21114  ->
                                   fun uu____21115  ->
                                     match (uu____21114, uu____21115) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21240 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21240 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21053
                               in
                            (match uu____21040 with
                             | (decls2,eqns,env01) ->
                                 let uu____21313 =
                                   let isDeclFun uu___92_21325 =
                                     match uu___92_21325 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21326 -> true
                                     | uu____21337 -> false  in
                                   let uu____21338 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____21338
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____21313 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____21378 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___93_21382  ->
                                 match uu___93_21382 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21383 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21389 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21389)))
                         in
                      if uu____21378
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
                   let uu____21441 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____21441
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
        let uu____21490 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____21490 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____21494 = encode_sigelt' env se  in
      match uu____21494 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21510 =
                  let uu____21511 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____21511  in
                [uu____21510]
            | uu____21512 ->
                let uu____21513 =
                  let uu____21516 =
                    let uu____21517 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21517  in
                  uu____21516 :: g  in
                let uu____21518 =
                  let uu____21521 =
                    let uu____21522 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21522  in
                  [uu____21521]  in
                FStar_List.append uu____21513 uu____21518
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
        let uu____21535 =
          let uu____21536 = FStar_Syntax_Subst.compress t  in
          uu____21536.FStar_Syntax_Syntax.n  in
        match uu____21535 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21540)) -> s = "opaque_to_smt"
        | uu____21541 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____21546 =
          let uu____21547 = FStar_Syntax_Subst.compress t  in
          uu____21547.FStar_Syntax_Syntax.n  in
        match uu____21546 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21551)) -> s = "uninterpreted_by_smt"
        | uu____21552 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21557 ->
          failwith "impossible -- removed by tc.fs"
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
                   (fun uu___94_22126  ->
                      match uu___94_22126 with
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
                       let uu___129_22282 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___129_22282.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___129_22282.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___129_22282.FStar_Syntax_Syntax.sigattrs)
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
                          FStar_Syntax_Syntax.lbattrs = uu____22321;_}::[]),uu____22322)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22345 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____22345 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____22374 =
                   let uu____22377 =
                     let uu____22378 =
                       let uu____22385 =
                         let uu____22386 =
                           let uu____22397 =
                             let uu____22398 =
                               let uu____22403 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____22403)  in
                             FStar_SMTEncoding_Util.mkEq uu____22398  in
                           ([[b2t_x]], [xx], uu____22397)  in
                         FStar_SMTEncoding_Util.mkForall uu____22386  in
                       (uu____22385,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____22378  in
                   [uu____22377]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22374
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22436,uu____22437) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_22446  ->
                  match uu___95_22446 with
                  | FStar_Syntax_Syntax.Discriminator uu____22447 -> true
                  | uu____22448 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22451,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22462 =
                     let uu____22463 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____22463.FStar_Ident.idText  in
                   uu____22462 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___96_22467  ->
                     match uu___96_22467 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22468 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22472) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_22489  ->
                  match uu___97_22489 with
                  | FStar_Syntax_Syntax.Projector uu____22490 -> true
                  | uu____22495 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____22498 = try_lookup_free_var env l  in
          (match uu____22498 with
           | FStar_Pervasives_Native.Some uu____22505 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___130_22509 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___130_22509.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___130_22509.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___130_22509.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22516) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22534) ->
          let uu____22543 = encode_sigelts env ses  in
          (match uu____22543 with
           | (g,env1) ->
               let uu____22560 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___98_22583  ->
                         match uu___98_22583 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22584;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22585;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22586;_}
                             -> false
                         | uu____22589 -> true))
                  in
               (match uu____22560 with
                | (g',inversions) ->
                    let uu____22604 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___99_22625  ->
                              match uu___99_22625 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22626 ->
                                  true
                              | uu____22637 -> false))
                       in
                    (match uu____22604 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22655,tps,k,uu____22658,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___100_22675  ->
                    match uu___100_22675 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22676 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22685 = c  in
              match uu____22685 with
              | (name,args,uu____22690,uu____22691,uu____22692) ->
                  let uu____22697 =
                    let uu____22698 =
                      let uu____22709 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22726  ->
                                match uu____22726 with
                                | (uu____22733,sort,uu____22735) -> sort))
                         in
                      (name, uu____22709, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____22698  in
                  [uu____22697]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____22762 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____22768 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____22768 FStar_Option.isNone))
               in
            if uu____22762
            then []
            else
              (let uu____22800 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____22800 with
               | (xxsym,xx) ->
                   let uu____22809 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____22848  ->
                             fun l  ->
                               match uu____22848 with
                               | (out,decls) ->
                                   let uu____22868 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____22868 with
                                    | (uu____22879,data_t) ->
                                        let uu____22881 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____22881 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____22927 =
                                                 let uu____22928 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____22928.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____22927 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____22939,indices) ->
                                                   indices
                                               | uu____22961 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____22985  ->
                                                         match uu____22985
                                                         with
                                                         | (x,uu____22991) ->
                                                             let uu____22992
                                                               =
                                                               let uu____22993
                                                                 =
                                                                 let uu____23000
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23000,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____22993
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____22992)
                                                    env)
                                                in
                                             let uu____23003 =
                                               encode_args indices env1  in
                                             (match uu____23003 with
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
                                                      let uu____23029 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23045
                                                                 =
                                                                 let uu____23050
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23050,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23045)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23029
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23053 =
                                                      let uu____23054 =
                                                        let uu____23059 =
                                                          let uu____23060 =
                                                            let uu____23065 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23065,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23060
                                                           in
                                                        (out, uu____23059)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23054
                                                       in
                                                    (uu____23053,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____22809 with
                    | (data_ax,decls) ->
                        let uu____23078 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23078 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23089 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23089 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23093 =
                                 let uu____23100 =
                                   let uu____23101 =
                                     let uu____23112 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23127 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23112,
                                       uu____23127)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23101
                                    in
                                 let uu____23142 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23100,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23142)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23093
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23145 =
            let uu____23158 =
              let uu____23159 = FStar_Syntax_Subst.compress k  in
              uu____23159.FStar_Syntax_Syntax.n  in
            match uu____23158 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23204 -> (tps, k)  in
          (match uu____23145 with
           | (formals,res) ->
               let uu____23227 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23227 with
                | (formals1,res1) ->
                    let uu____23238 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23238 with
                     | (vars,guards,env',binder_decls,uu____23263) ->
                         let arity = FStar_List.length vars  in
                         let uu____23277 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____23277 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23300 =
                                  let uu____23307 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23307)  in
                                FStar_SMTEncoding_Util.mkApp uu____23300  in
                              let uu____23316 =
                                let tname_decl =
                                  let uu____23326 =
                                    let uu____23327 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23359  ->
                                              match uu____23359 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23372 = varops.next_id ()  in
                                    (tname, uu____23327,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23372, false)
                                     in
                                  constructor_or_logic_type_decl uu____23326
                                   in
                                let uu____23381 =
                                  match vars with
                                  | [] ->
                                      let uu____23394 =
                                        let uu____23395 =
                                          let uu____23398 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23398
                                           in
                                        push_free_var env1 t arity tname
                                          uu____23395
                                         in
                                      ([], uu____23394)
                                  | uu____23409 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____23418 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23418
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____23432 =
                                          let uu____23439 =
                                            let uu____23440 =
                                              let uu____23455 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23455)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23440
                                             in
                                          (uu____23439,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23432
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____23381 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23316 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23495 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____23495 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23513 =
                                               let uu____23514 =
                                                 let uu____23521 =
                                                   let uu____23522 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23522
                                                    in
                                                 (uu____23521,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23514
                                                in
                                             [uu____23513]
                                           else []  in
                                         let uu____23526 =
                                           let uu____23529 =
                                             let uu____23532 =
                                               let uu____23533 =
                                                 let uu____23540 =
                                                   let uu____23541 =
                                                     let uu____23552 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____23552)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23541
                                                    in
                                                 (uu____23540,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23533
                                                in
                                             [uu____23532]  in
                                           FStar_List.append karr uu____23529
                                            in
                                         FStar_List.append decls1 uu____23526
                                      in
                                   let aux =
                                     let uu____23568 =
                                       let uu____23571 =
                                         inversion_axioms tapp vars  in
                                       let uu____23574 =
                                         let uu____23577 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____23577]  in
                                       FStar_List.append uu____23571
                                         uu____23574
                                        in
                                     FStar_List.append kindingAx uu____23568
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23584,uu____23585,uu____23586,uu____23587,uu____23588)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23596,t,uu____23598,n_tps,uu____23600) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____23608 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____23608 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____23648 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____23648 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____23669 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____23669 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____23683 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____23683 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____23753 =
                                            mk_term_projector_name d x  in
                                          (uu____23753,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____23755 =
                                  let uu____23774 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23774, true)
                                   in
                                FStar_All.pipe_right uu____23755
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
                              let uu____23813 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____23813 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23825::uu____23826 ->
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
                                         let uu____23871 =
                                           let uu____23882 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____23882)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____23871
                                     | uu____23907 -> tok_typing  in
                                   let uu____23916 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____23916 with
                                    | (vars',guards',env'',decls_formals,uu____23941)
                                        ->
                                        let uu____23954 =
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
                                        (match uu____23954 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____23985 ->
                                                   let uu____23992 =
                                                     let uu____23993 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____23993
                                                      in
                                                   [uu____23992]
                                                in
                                             let encode_elim uu____24003 =
                                               let uu____24004 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24004 with
                                               | (head1,args) ->
                                                   let uu____24047 =
                                                     let uu____24048 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24048.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24047 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24058;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24059;_},uu____24060)
                                                        ->
                                                        let uu____24065 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24065
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24078
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24078
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
                                                                    uu____24121
                                                                    ->
                                                                    let uu____24122
                                                                    =
                                                                    let uu____24127
                                                                    =
                                                                    let uu____24128
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24128
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24127)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24122
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24144
                                                                    =
                                                                    let uu____24145
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24145
                                                                     in
                                                                    if
                                                                    uu____24144
                                                                    then
                                                                    let uu____24158
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24158]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24160
                                                                    =
                                                                    let uu____24173
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24223
                                                                     ->
                                                                    fun
                                                                    uu____24224
                                                                     ->
                                                                    match 
                                                                    (uu____24223,
                                                                    uu____24224)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24319
                                                                    =
                                                                    let uu____24326
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24326
                                                                     in
                                                                    (match uu____24319
                                                                    with
                                                                    | 
                                                                    (uu____24339,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24347
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24347
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24349
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24349
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
                                                                    uu____24173
                                                                     in
                                                                  (match uu____24160
                                                                   with
                                                                   | 
                                                                   (uu____24364,arg_vars,elim_eqns_or_guards,uu____24367)
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
                                                                    let uu____24395
                                                                    =
                                                                    let uu____24402
                                                                    =
                                                                    let uu____24403
                                                                    =
                                                                    let uu____24414
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24425
                                                                    =
                                                                    let uu____24426
                                                                    =
                                                                    let uu____24431
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24431)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24426
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24414,
                                                                    uu____24425)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24403
                                                                     in
                                                                    (uu____24402,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24395
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24454
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24454,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24456
                                                                    =
                                                                    let uu____24463
                                                                    =
                                                                    let uu____24464
                                                                    =
                                                                    let uu____24475
                                                                    =
                                                                    let uu____24480
                                                                    =
                                                                    let uu____24483
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____24483]
                                                                     in
                                                                    [uu____24480]
                                                                     in
                                                                    let uu____24488
                                                                    =
                                                                    let uu____24489
                                                                    =
                                                                    let uu____24494
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____24495
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____24494,
                                                                    uu____24495)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24489
                                                                     in
                                                                    (uu____24475,
                                                                    [x],
                                                                    uu____24488)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24464
                                                                     in
                                                                    let uu____24514
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24463,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24514)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24456
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24521
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
                                                                    (let uu____24549
                                                                    =
                                                                    let uu____24550
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24550
                                                                    dapp1  in
                                                                    [uu____24549])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24521
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____24557
                                                                    =
                                                                    let uu____24564
                                                                    =
                                                                    let uu____24565
                                                                    =
                                                                    let uu____24576
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24587
                                                                    =
                                                                    let uu____24588
                                                                    =
                                                                    let uu____24593
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____24593)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24588
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24576,
                                                                    uu____24587)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24565
                                                                     in
                                                                    (uu____24564,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24557)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____24613 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24613
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24626
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24626
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
                                                                    uu____24669
                                                                    ->
                                                                    let uu____24670
                                                                    =
                                                                    let uu____24675
                                                                    =
                                                                    let uu____24676
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24676
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24675)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24670
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24692
                                                                    =
                                                                    let uu____24693
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24693
                                                                     in
                                                                    if
                                                                    uu____24692
                                                                    then
                                                                    let uu____24706
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24706]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24708
                                                                    =
                                                                    let uu____24721
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24771
                                                                     ->
                                                                    fun
                                                                    uu____24772
                                                                     ->
                                                                    match 
                                                                    (uu____24771,
                                                                    uu____24772)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24867
                                                                    =
                                                                    let uu____24874
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24874
                                                                     in
                                                                    (match uu____24867
                                                                    with
                                                                    | 
                                                                    (uu____24887,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24895
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24895
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24897
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
                                                                    uu____24721
                                                                     in
                                                                  (match uu____24708
                                                                   with
                                                                   | 
                                                                   (uu____24912,arg_vars,elim_eqns_or_guards,uu____24915)
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
                                                                    let uu____24943
                                                                    =
                                                                    let uu____24950
                                                                    =
                                                                    let uu____24951
                                                                    =
                                                                    let uu____24962
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24973
                                                                    =
                                                                    let uu____24974
                                                                    =
                                                                    let uu____24979
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24979)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24974
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24962,
                                                                    uu____24973)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24951
                                                                     in
                                                                    (uu____24950,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24943
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25002
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25002,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25004
                                                                    =
                                                                    let uu____25011
                                                                    =
                                                                    let uu____25012
                                                                    =
                                                                    let uu____25023
                                                                    =
                                                                    let uu____25028
                                                                    =
                                                                    let uu____25031
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25031]
                                                                     in
                                                                    [uu____25028]
                                                                     in
                                                                    let uu____25036
                                                                    =
                                                                    let uu____25037
                                                                    =
                                                                    let uu____25042
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25043
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25042,
                                                                    uu____25043)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25037
                                                                     in
                                                                    (uu____25023,
                                                                    [x],
                                                                    uu____25036)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25012
                                                                     in
                                                                    let uu____25062
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25011,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25062)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25004
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25069
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
                                                                    (let uu____25097
                                                                    =
                                                                    let uu____25098
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25098
                                                                    dapp1  in
                                                                    [uu____25097])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25069
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25105
                                                                    =
                                                                    let uu____25112
                                                                    =
                                                                    let uu____25113
                                                                    =
                                                                    let uu____25124
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25135
                                                                    =
                                                                    let uu____25136
                                                                    =
                                                                    let uu____25141
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25141)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25136
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25124,
                                                                    uu____25135)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25113
                                                                     in
                                                                    (uu____25112,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25105)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____25160 ->
                                                        ((let uu____25162 =
                                                            let uu____25167 =
                                                              let uu____25168
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25169
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25168
                                                                uu____25169
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25167)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25162);
                                                         ([], [])))
                                                in
                                             let uu____25174 = encode_elim ()
                                                in
                                             (match uu____25174 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25194 =
                                                      let uu____25197 =
                                                        let uu____25200 =
                                                          let uu____25203 =
                                                            let uu____25206 =
                                                              let uu____25207
                                                                =
                                                                let uu____25218
                                                                  =
                                                                  let uu____25221
                                                                    =
                                                                    let uu____25222
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25222
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25221
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25218)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25207
                                                               in
                                                            [uu____25206]  in
                                                          let uu____25227 =
                                                            let uu____25230 =
                                                              let uu____25233
                                                                =
                                                                let uu____25236
                                                                  =
                                                                  let uu____25239
                                                                    =
                                                                    let uu____25242
                                                                    =
                                                                    let uu____25245
                                                                    =
                                                                    let uu____25246
                                                                    =
                                                                    let uu____25253
                                                                    =
                                                                    let uu____25254
                                                                    =
                                                                    let uu____25265
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25265)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25254
                                                                     in
                                                                    (uu____25253,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25246
                                                                     in
                                                                    let uu____25278
                                                                    =
                                                                    let uu____25281
                                                                    =
                                                                    let uu____25282
                                                                    =
                                                                    let uu____25289
                                                                    =
                                                                    let uu____25290
                                                                    =
                                                                    let uu____25301
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25312
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25301,
                                                                    uu____25312)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25290
                                                                     in
                                                                    (uu____25289,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25282
                                                                     in
                                                                    [uu____25281]
                                                                     in
                                                                    uu____25245
                                                                    ::
                                                                    uu____25278
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25242
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25239
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25236
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25233
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25230
                                                             in
                                                          FStar_List.append
                                                            uu____25203
                                                            uu____25227
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25200
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25197
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25194
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
           (fun uu____25358  ->
              fun se  ->
                match uu____25358 with
                | (g,env1) ->
                    let uu____25378 = encode_sigelt env1 se  in
                    (match uu____25378 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25435 =
        match uu____25435 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25467 ->
                 ((i + (Prims.parse_int "1")), [], env1)
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
                 ((let uu____25473 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____25473
                   then
                     let uu____25474 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____25475 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____25476 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25474 uu____25475 uu____25476
                   else ());
                  (let uu____25478 = encode_term t1 env1  in
                   match uu____25478 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____25494 =
                         let uu____25501 =
                           let uu____25502 =
                             let uu____25503 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____25503
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____25502  in
                         new_term_constant_from_string env1 x uu____25501  in
                       (match uu____25494 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____25519 = FStar_Options.log_queries ()
                                 in
                              if uu____25519
                              then
                                let uu____25522 =
                                  let uu____25523 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____25524 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____25525 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25523 uu____25524 uu____25525
                                   in
                                FStar_Pervasives_Native.Some uu____25522
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25541,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____25555 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____25555 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25578,se,uu____25580) ->
                 let uu____25585 = encode_sigelt env1 se  in
                 (match uu____25585 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25602,se) ->
                 let uu____25608 = encode_sigelt env1 se  in
                 (match uu____25608 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____25625 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____25625 with | (uu____25648,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____25660 'Auu____25661 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____25661,'Auu____25660)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25729  ->
              match uu____25729 with
              | (l,uu____25741,uu____25742) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____25788  ->
              match uu____25788 with
              | (l,uu____25802,uu____25803) ->
                  let uu____25812 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____25813 =
                    let uu____25816 =
                      let uu____25817 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____25817  in
                    [uu____25816]  in
                  uu____25812 :: uu____25813))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____25842 =
      let uu____25845 =
        let uu____25846 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____25849 =
          let uu____25850 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____25850 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____25846;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____25849
        }  in
      [uu____25845]  in
    FStar_ST.op_Colon_Equals last_env uu____25842
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____25880 = FStar_ST.op_Bang last_env  in
      match uu____25880 with
      | [] -> failwith "No env; call init first!"
      | e::uu____25907 ->
          let uu___131_25910 = e  in
          let uu____25911 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___131_25910.bindings);
            depth = (uu___131_25910.depth);
            tcenv;
            warn = (uu___131_25910.warn);
            cache = (uu___131_25910.cache);
            nolabels = (uu___131_25910.nolabels);
            use_zfuel_name = (uu___131_25910.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_25910.encode_non_total_function_typ);
            current_module_name = uu____25911
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____25915 = FStar_ST.op_Bang last_env  in
    match uu____25915 with
    | [] -> failwith "Empty env stack"
    | uu____25941::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____25970  ->
    let uu____25971 = FStar_ST.op_Bang last_env  in
    match uu____25971 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___132_26005 = hd1  in
          {
            bindings = (uu___132_26005.bindings);
            depth = (uu___132_26005.depth);
            tcenv = (uu___132_26005.tcenv);
            warn = (uu___132_26005.warn);
            cache = refs;
            nolabels = (uu___132_26005.nolabels);
            use_zfuel_name = (uu___132_26005.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_26005.encode_non_total_function_typ);
            current_module_name = (uu___132_26005.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____26031  ->
    let uu____26032 = FStar_ST.op_Bang last_env  in
    match uu____26032 with
    | [] -> failwith "Popping an empty stack"
    | uu____26058::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____26122::uu____26123,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___133_26131 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___133_26131.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___133_26131.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___133_26131.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26132 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26147 =
        let uu____26150 =
          let uu____26151 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26151  in
        let uu____26152 = open_fact_db_tags env  in uu____26150 ::
          uu____26152
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26147
  
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
      let uu____26174 = encode_sigelt env se  in
      match uu____26174 with
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
        let uu____26210 = FStar_Options.log_queries ()  in
        if uu____26210
        then
          let uu____26213 =
            let uu____26214 =
              let uu____26215 =
                let uu____26216 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26216 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26215  in
            FStar_SMTEncoding_Term.Caption uu____26214  in
          uu____26213 :: decls
        else decls  in
      (let uu____26227 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26227
       then
         let uu____26228 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26228
       else ());
      (let env =
         let uu____26231 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26231 tcenv  in
       let uu____26232 = encode_top_level_facts env se  in
       match uu____26232 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26246 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26246)))
  
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
      (let uu____26258 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26258
       then
         let uu____26259 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26259
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26294  ->
                 fun se  ->
                   match uu____26294 with
                   | (g,env2) ->
                       let uu____26314 = encode_top_level_facts env2 se  in
                       (match uu____26314 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26337 =
         encode_signature
           (let uu___134_26346 = env  in
            {
              bindings = (uu___134_26346.bindings);
              depth = (uu___134_26346.depth);
              tcenv = (uu___134_26346.tcenv);
              warn = false;
              cache = (uu___134_26346.cache);
              nolabels = (uu___134_26346.nolabels);
              use_zfuel_name = (uu___134_26346.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_26346.encode_non_total_function_typ);
              current_module_name = (uu___134_26346.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26337 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26363 = FStar_Options.log_queries ()  in
             if uu____26363
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___135_26371 = env1  in
               {
                 bindings = (uu___135_26371.bindings);
                 depth = (uu___135_26371.depth);
                 tcenv = (uu___135_26371.tcenv);
                 warn = true;
                 cache = (uu___135_26371.cache);
                 nolabels = (uu___135_26371.nolabels);
                 use_zfuel_name = (uu___135_26371.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___135_26371.encode_non_total_function_typ);
                 current_module_name = (uu___135_26371.current_module_name)
               });
            (let uu____26373 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____26373
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
        (let uu____26425 =
           let uu____26426 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____26426.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26425);
        (let env =
           let uu____26428 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____26428 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____26440 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26475 = aux rest  in
                 (match uu____26475 with
                  | (out,rest1) ->
                      let t =
                        let uu____26505 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____26505 with
                        | FStar_Pervasives_Native.Some uu____26510 ->
                            let uu____26511 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____26511
                              x.FStar_Syntax_Syntax.sort
                        | uu____26512 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____26516 =
                        let uu____26519 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___136_26522 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_26522.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_26522.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____26519 :: out  in
                      (uu____26516, rest1))
             | uu____26527 -> ([], bindings1)  in
           let uu____26534 = aux bindings  in
           match uu____26534 with
           | (closing,bindings1) ->
               let uu____26559 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____26559, bindings1)
            in
         match uu____26440 with
         | (q1,bindings1) ->
             let uu____26582 =
               let uu____26587 =
                 FStar_List.filter
                   (fun uu___101_26592  ->
                      match uu___101_26592 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26593 ->
                          false
                      | uu____26600 -> true) bindings1
                  in
               encode_env_bindings env uu____26587  in
             (match uu____26582 with
              | (env_decls,env1) ->
                  ((let uu____26618 =
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
                    if uu____26618
                    then
                      let uu____26619 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26619
                    else ());
                   (let uu____26621 = encode_formula q1 env1  in
                    match uu____26621 with
                    | (phi,qdecls) ->
                        let uu____26642 =
                          let uu____26647 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26647 phi
                           in
                        (match uu____26642 with
                         | (labels,phi1) ->
                             let uu____26664 = encode_labels labels  in
                             (match uu____26664 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____26701 =
                                      let uu____26708 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____26709 =
                                        varops.mk_unique "@query"  in
                                      (uu____26708,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26709)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26701
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
  