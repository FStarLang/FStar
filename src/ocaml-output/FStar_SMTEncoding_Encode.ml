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
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = uu____5669;
              FStar_Syntax_Syntax.pos = uu____5670;
              FStar_Syntax_Syntax.vars = uu____5671;_},FStar_Syntax_Syntax.Meta_quoted
            (qt,qi))
           ->
           let tv =
             let uu____5683 = FStar_Reflection_Basic.inspect qt  in
             FStar_Reflection_Basic.embed_term_view t.FStar_Syntax_Syntax.pos
               uu____5683
              in
           let t1 =
             let uu____5687 =
               let uu____5696 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____5696]  in
             FStar_Syntax_Util.mk_app FStar_Reflection_Data.fstar_refl_pack
               uu____5687
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5698) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5708 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____5708, [])
       | FStar_Syntax_Syntax.Tm_type uu____5711 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5715) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____5740 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5740 with
            | (binders1,res) ->
                let uu____5751 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5751
                then
                  let uu____5756 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5756 with
                   | (vars,guards,env',decls,uu____5781) ->
                       let fsym =
                         let uu____5799 = varops.fresh "f"  in
                         (uu____5799, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5802 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___111_5811 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___111_5811.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___111_5811.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___111_5811.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___111_5811.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___111_5811.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___111_5811.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___111_5811.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___111_5811.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___111_5811.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___111_5811.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___111_5811.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___111_5811.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___111_5811.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___111_5811.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___111_5811.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___111_5811.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___111_5811.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___111_5811.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___111_5811.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___111_5811.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___111_5811.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___111_5811.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___111_5811.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___111_5811.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___111_5811.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___111_5811.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___111_5811.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___111_5811.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___111_5811.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___111_5811.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___111_5811.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___111_5811.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___111_5811.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___111_5811.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____5802 with
                        | (pre_opt,res_t) ->
                            let uu____5822 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5822 with
                             | (res_pred,decls') ->
                                 let uu____5833 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5846 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____5846, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5850 =
                                         encode_formula pre env'  in
                                       (match uu____5850 with
                                        | (guard,decls0) ->
                                            let uu____5863 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____5863, decls0))
                                    in
                                 (match uu____5833 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____5875 =
                                          let uu____5886 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____5886)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5875
                                         in
                                      let cvars =
                                        let uu____5904 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____5904
                                          (FStar_List.filter
                                             (fun uu____5918  ->
                                                match uu____5918 with
                                                | (x,uu____5924) ->
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
                                      let uu____5943 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____5943 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5951 =
                                             let uu____5952 =
                                               let uu____5959 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5959)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5952
                                              in
                                           (uu____5951,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____5979 =
                                               let uu____5980 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____5980
                                                in
                                             varops.mk_unique uu____5979  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____5991 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____5991
                                             then
                                               let uu____5994 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____5994
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
                                             let uu____6002 =
                                               let uu____6009 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6009)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6002
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
                                             let uu____6021 =
                                               let uu____6028 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6028,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6021
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
                                             let uu____6049 =
                                               let uu____6056 =
                                                 let uu____6057 =
                                                   let uu____6068 =
                                                     let uu____6069 =
                                                       let uu____6074 =
                                                         let uu____6075 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6075
                                                          in
                                                       (f_has_t, uu____6074)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6069
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6068)
                                                    in
                                                 mkForall_fuel uu____6057  in
                                               (uu____6056,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6049
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6098 =
                                               let uu____6105 =
                                                 let uu____6106 =
                                                   let uu____6117 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6117)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6106
                                                  in
                                               (uu____6105,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6098
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
                                           ((let uu____6142 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6142);
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
                     let uu____6157 =
                       let uu____6164 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6164,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6157  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6176 =
                       let uu____6183 =
                         let uu____6184 =
                           let uu____6195 =
                             let uu____6196 =
                               let uu____6201 =
                                 let uu____6202 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6202
                                  in
                               (f_has_t, uu____6201)  in
                             FStar_SMTEncoding_Util.mkImp uu____6196  in
                           ([[f_has_t]], [fsym], uu____6195)  in
                         mkForall_fuel uu____6184  in
                       (uu____6183, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6176  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6229 ->
           let uu____6236 =
             let uu____6241 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6241 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6248;
                 FStar_Syntax_Syntax.vars = uu____6249;_} ->
                 let uu____6256 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6256 with
                  | (b,f1) ->
                      let uu____6281 =
                        let uu____6282 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6282  in
                      (uu____6281, f1))
             | uu____6291 -> failwith "impossible"  in
           (match uu____6236 with
            | (x,f) ->
                let uu____6302 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6302 with
                 | (base_t,decls) ->
                     let uu____6313 = gen_term_var env x  in
                     (match uu____6313 with
                      | (x1,xtm,env') ->
                          let uu____6327 = encode_formula f env'  in
                          (match uu____6327 with
                           | (refinement,decls') ->
                               let uu____6338 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6338 with
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
                                      let uu____6354 =
                                        let uu____6357 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6364 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6357
                                          uu____6364
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6354
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6397  ->
                                              match uu____6397 with
                                              | (y,uu____6403) ->
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
                                    let uu____6436 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6436 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6444 =
                                           let uu____6445 =
                                             let uu____6452 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6452)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6445
                                            in
                                         (uu____6444,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6473 =
                                             let uu____6474 =
                                               let uu____6475 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6475
                                                in
                                             Prims.strcat module_name
                                               uu____6474
                                              in
                                           varops.mk_unique uu____6473  in
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
                                           let uu____6489 =
                                             let uu____6496 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6496)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6489
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
                                           let uu____6511 =
                                             let uu____6518 =
                                               let uu____6519 =
                                                 let uu____6530 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6530)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6519
                                                in
                                             (uu____6518,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6511
                                            in
                                         let t_kinding =
                                           let uu____6548 =
                                             let uu____6555 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6555,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6548
                                            in
                                         let t_interp =
                                           let uu____6573 =
                                             let uu____6580 =
                                               let uu____6581 =
                                                 let uu____6592 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6592)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6581
                                                in
                                             let uu____6615 =
                                               let uu____6618 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6618
                                                in
                                             (uu____6580, uu____6615,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6573
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____6625 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6625);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6655 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6655  in
           let uu____6656 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____6656 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6668 =
                    let uu____6675 =
                      let uu____6676 =
                        let uu____6677 =
                          let uu____6678 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6678
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____6677  in
                      varops.mk_unique uu____6676  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6675)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6668  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6683 ->
           let uu____6698 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6698 with
            | (head1,args_e) ->
                let uu____6739 =
                  let uu____6752 =
                    let uu____6753 = FStar_Syntax_Subst.compress head1  in
                    uu____6753.FStar_Syntax_Syntax.n  in
                  (uu____6752, args_e)  in
                (match uu____6739 with
                 | uu____6768 when head_redex env head1 ->
                     let uu____6781 = whnf env t  in
                     encode_term uu____6781 env
                 | uu____6782 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6801 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6815;
                       FStar_Syntax_Syntax.vars = uu____6816;_},uu____6817),uu____6818::
                    (v1,uu____6820)::(v2,uu____6822)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6873 = encode_term v1 env  in
                     (match uu____6873 with
                      | (v11,decls1) ->
                          let uu____6884 = encode_term v2 env  in
                          (match uu____6884 with
                           | (v21,decls2) ->
                               let uu____6895 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6895,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6899::(v1,uu____6901)::(v2,uu____6903)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6950 = encode_term v1 env  in
                     (match uu____6950 with
                      | (v11,decls1) ->
                          let uu____6961 = encode_term v2 env  in
                          (match uu____6961 with
                           | (v21,decls2) ->
                               let uu____6972 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6972,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6976)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7002)::(rng,uu____7004)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7039) ->
                     let e0 =
                       let uu____7057 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7057
                        in
                     ((let uu____7065 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7065
                       then
                         let uu____7066 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7066
                       else ());
                      (let e =
                         let uu____7071 =
                           let uu____7072 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7073 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7072
                             uu____7073
                            in
                         uu____7071 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7082),(arg,uu____7084)::[]) -> encode_term arg env
                 | uu____7109 ->
                     let uu____7122 = encode_args args_e env  in
                     (match uu____7122 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7177 = encode_term head1 env  in
                            match uu____7177 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7241 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7241 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7319  ->
                                                 fun uu____7320  ->
                                                   match (uu____7319,
                                                           uu____7320)
                                                   with
                                                   | ((bv,uu____7342),
                                                      (a,uu____7344)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7362 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7362
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7367 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7367 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7382 =
                                                   let uu____7389 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7398 =
                                                     let uu____7399 =
                                                       let uu____7400 =
                                                         let uu____7401 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7401
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7400
                                                        in
                                                     varops.mk_unique
                                                       uu____7399
                                                      in
                                                   (uu____7389,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7398)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7382
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7418 = lookup_free_var_sym env fv  in
                            match uu____7418 with
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
                                   FStar_Syntax_Syntax.pos = uu____7450;
                                   FStar_Syntax_Syntax.vars = uu____7451;_},uu____7452)
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
                                   FStar_Syntax_Syntax.pos = uu____7463;
                                   FStar_Syntax_Syntax.vars = uu____7464;_},uu____7465)
                                ->
                                let uu____7470 =
                                  let uu____7471 =
                                    let uu____7476 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7476
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7471
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7470
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7506 =
                                  let uu____7507 =
                                    let uu____7512 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7512
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7507
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7506
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7541,(FStar_Util.Inl t1,uu____7543),uu____7544)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7593,(FStar_Util.Inr c,uu____7595),uu____7596)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7645 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7672 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7672
                                  in
                               let uu____7673 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7673 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7689;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7690;_},uu____7691)
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
                                     | uu____7705 ->
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
           let uu____7754 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7754 with
            | (bs1,body1,opening) ->
                let fallback uu____7777 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7784 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7784, [decl])  in
                let is_impure rc =
                  let uu____7791 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7791 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7801 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____7801
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____7821 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7821
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____7825 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7825)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7832 =
                         let uu____7837 =
                           let uu____7838 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7838
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7837)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7832);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7840 =
                       (is_impure rc) &&
                         (let uu____7842 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____7842)
                        in
                     if uu____7840
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____7849 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7849 with
                        | (vars,guards,envbody,decls,uu____7874) ->
                            let body2 =
                              let uu____7888 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____7888
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____7890 = encode_term body2 envbody  in
                            (match uu____7890 with
                             | (body3,decls') ->
                                 let uu____7901 =
                                   let uu____7910 = codomain_eff rc  in
                                   match uu____7910 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7929 = encode_term tfun env
                                          in
                                       (match uu____7929 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7901 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7961 =
                                          let uu____7972 =
                                            let uu____7973 =
                                              let uu____7978 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7978, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7973
                                             in
                                          ([], vars, uu____7972)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____7961
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
                                            let uu____7990 =
                                              let uu____7993 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____7993
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____7990
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8012 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8012 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8020 =
                                             let uu____8021 =
                                               let uu____8028 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8028)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8021
                                              in
                                           (uu____8020,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8039 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8039 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8050 =
                                                    let uu____8051 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8051 = cache_size
                                                     in
                                                  if uu____8050
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
                                                    let uu____8067 =
                                                      let uu____8068 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8068
                                                       in
                                                    varops.mk_unique
                                                      uu____8067
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
                                                  let uu____8075 =
                                                    let uu____8082 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8082)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8075
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
                                                      let uu____8100 =
                                                        let uu____8101 =
                                                          let uu____8108 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8108,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8101
                                                         in
                                                      [uu____8100]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8121 =
                                                    let uu____8128 =
                                                      let uu____8129 =
                                                        let uu____8140 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8140)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8129
                                                       in
                                                    (uu____8128,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8121
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
                                                ((let uu____8157 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8157);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8160,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8161;
                          FStar_Syntax_Syntax.lbunivs = uu____8162;
                          FStar_Syntax_Syntax.lbtyp = uu____8163;
                          FStar_Syntax_Syntax.lbeff = uu____8164;
                          FStar_Syntax_Syntax.lbdef = uu____8165;
                          FStar_Syntax_Syntax.lbattrs = uu____8166;_}::uu____8167),uu____8168)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8198;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8200;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8202;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8226 ->
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
              let uu____8296 =
                let uu____8301 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8301 env  in
              match uu____8296 with
              | (ee1,decls1) ->
                  let uu____8322 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8322 with
                   | (xs,e21) ->
                       let uu____8347 = FStar_List.hd xs  in
                       (match uu____8347 with
                        | (x1,uu____8361) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8363 = encode_body e21 env'  in
                            (match uu____8363 with
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
            let uu____8395 =
              let uu____8402 =
                let uu____8403 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8403  in
              gen_term_var env uu____8402  in
            match uu____8395 with
            | (scrsym,scr',env1) ->
                let uu____8411 = encode_term e env1  in
                (match uu____8411 with
                 | (scr,decls) ->
                     let uu____8422 =
                       let encode_branch b uu____8447 =
                         match uu____8447 with
                         | (else_case,decls1) ->
                             let uu____8466 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8466 with
                              | (p,w,br) ->
                                  let uu____8492 = encode_pat env1 p  in
                                  (match uu____8492 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8529  ->
                                                   match uu____8529 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8536 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8558 =
                                               encode_term w1 env2  in
                                             (match uu____8558 with
                                              | (w2,decls2) ->
                                                  let uu____8571 =
                                                    let uu____8572 =
                                                      let uu____8577 =
                                                        let uu____8578 =
                                                          let uu____8583 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8583)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8578
                                                         in
                                                      (guard, uu____8577)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8572
                                                     in
                                                  (uu____8571, decls2))
                                          in
                                       (match uu____8536 with
                                        | (guard1,decls2) ->
                                            let uu____8596 =
                                              encode_br br env2  in
                                            (match uu____8596 with
                                             | (br1,decls3) ->
                                                 let uu____8609 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8609,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8422 with
                      | (match_tm,decls1) ->
                          let uu____8628 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8628, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____8668 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____8668
       then
         let uu____8669 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8669
       else ());
      (let uu____8671 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8671 with
       | (vars,pat_term) ->
           let uu____8688 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8741  ->
                     fun v1  ->
                       match uu____8741 with
                       | (env1,vars1) ->
                           let uu____8793 = gen_term_var env1 v1  in
                           (match uu____8793 with
                            | (xx,uu____8815,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8688 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8894 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8895 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8896 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8904 = encode_const c env1  in
                      (match uu____8904 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8918::uu____8919 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8922 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8945 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____8945 with
                        | (uu____8952,uu____8953::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8956 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8989  ->
                                  match uu____8989 with
                                  | (arg,uu____8997) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9003 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9003))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9030) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9061 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9084 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9128  ->
                                  match uu____9128 with
                                  | (arg,uu____9142) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9148 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9148))
                         in
                      FStar_All.pipe_right uu____9084 FStar_List.flatten
                   in
                let pat_term1 uu____9176 = encode_term pat_term env1  in
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
      let uu____9186 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9224  ->
                fun uu____9225  ->
                  match (uu____9224, uu____9225) with
                  | ((tms,decls),(t,uu____9261)) ->
                      let uu____9282 = encode_term t env  in
                      (match uu____9282 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9186 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9339 = FStar_Syntax_Util.list_elements e  in
        match uu____9339 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9360 =
          let uu____9375 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9375 FStar_Syntax_Util.head_and_args  in
        match uu____9360 with
        | (head1,args) ->
            let uu____9414 =
              let uu____9427 =
                let uu____9428 = FStar_Syntax_Util.un_uinst head1  in
                uu____9428.FStar_Syntax_Syntax.n  in
              (uu____9427, args)  in
            (match uu____9414 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9442,uu____9443)::(e,uu____9445)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9480 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9516 =
            let uu____9531 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9531 FStar_Syntax_Util.head_and_args
             in
          match uu____9516 with
          | (head1,args) ->
              let uu____9572 =
                let uu____9585 =
                  let uu____9586 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9586.FStar_Syntax_Syntax.n  in
                (uu____9585, args)  in
              (match uu____9572 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9603)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9630 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9652 = smt_pat_or1 t1  in
            (match uu____9652 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9668 = list_elements1 e  in
                 FStar_All.pipe_right uu____9668
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9686 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9686
                           (FStar_List.map one_pat)))
             | uu____9697 ->
                 let uu____9702 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9702])
        | uu____9723 ->
            let uu____9726 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9726]
         in
      let uu____9747 =
        let uu____9766 =
          let uu____9767 = FStar_Syntax_Subst.compress t  in
          uu____9767.FStar_Syntax_Syntax.n  in
        match uu____9766 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9806 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9806 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9849;
                        FStar_Syntax_Syntax.effect_name = uu____9850;
                        FStar_Syntax_Syntax.result_typ = uu____9851;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9853)::(post,uu____9855)::(pats,uu____9857)::[];
                        FStar_Syntax_Syntax.flags = uu____9858;_}
                      ->
                      let uu____9899 = lemma_pats pats  in
                      (binders1, pre, post, uu____9899)
                  | uu____9916 -> failwith "impos"))
        | uu____9935 -> failwith "Impos"  in
      match uu____9747 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___112_9983 = env  in
            {
              bindings = (uu___112_9983.bindings);
              depth = (uu___112_9983.depth);
              tcenv = (uu___112_9983.tcenv);
              warn = (uu___112_9983.warn);
              cache = (uu___112_9983.cache);
              nolabels = (uu___112_9983.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___112_9983.encode_non_total_function_typ);
              current_module_name = (uu___112_9983.current_module_name)
            }  in
          let uu____9984 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9984 with
           | (vars,guards,env2,decls,uu____10009) ->
               let uu____10022 =
                 let uu____10037 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10091 =
                             let uu____10102 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10102
                               FStar_List.unzip
                              in
                           match uu____10091 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10037 FStar_List.unzip  in
               (match uu____10022 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___113_10254 = env2  in
                      {
                        bindings = (uu___113_10254.bindings);
                        depth = (uu___113_10254.depth);
                        tcenv = (uu___113_10254.tcenv);
                        warn = (uu___113_10254.warn);
                        cache = (uu___113_10254.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___113_10254.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___113_10254.encode_non_total_function_typ);
                        current_module_name =
                          (uu___113_10254.current_module_name)
                      }  in
                    let uu____10255 =
                      let uu____10260 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10260 env3  in
                    (match uu____10255 with
                     | (pre1,decls'') ->
                         let uu____10267 =
                           let uu____10272 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10272 env3  in
                         (match uu____10267 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10282 =
                                let uu____10283 =
                                  let uu____10294 =
                                    let uu____10295 =
                                      let uu____10300 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10300, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10295
                                     in
                                  (pats, vars, uu____10294)  in
                                FStar_SMTEncoding_Util.mkForall uu____10283
                                 in
                              (uu____10282, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____10313 = FStar_Syntax_Util.head_and_args t  in
      match uu____10313 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10372::(x,uu____10374)::(t1,uu____10376)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10423 = encode_term x env  in
               (match uu____10423 with
                | (x1,decls) ->
                    let uu____10436 = encode_term t1 env  in
                    (match uu____10436 with
                     | (t2,decls') ->
                         let uu____10449 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10449, (FStar_List.append decls decls'))))
           | uu____10452 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10475 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10475
        then
          let uu____10476 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10477 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10476 uu____10477
        else ()  in
      let enc f r l =
        let uu____10510 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10538 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10538 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10510 with
        | (decls,args) ->
            let uu____10567 =
              let uu___114_10568 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10568.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10568.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10567, decls)
         in
      let const_op f r uu____10599 =
        let uu____10612 = f r  in (uu____10612, [])  in
      let un_op f l =
        let uu____10631 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10631  in
      let bin_op f uu___88_10647 =
        match uu___88_10647 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10658 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10692 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10715  ->
                 match uu____10715 with
                 | (t,uu____10729) ->
                     let uu____10730 = encode_formula t env  in
                     (match uu____10730 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10692 with
        | (decls,phis) ->
            let uu____10759 =
              let uu___115_10760 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___115_10760.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___115_10760.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10759, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10821  ->
               match uu____10821 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10840) -> false
                    | uu____10841 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10856 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10856
        else
          (let uu____10870 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10870 r rf)
         in
      let mk_imp1 r uu___89_10895 =
        match uu___89_10895 with
        | (lhs,uu____10901)::(rhs,uu____10903)::[] ->
            let uu____10930 = encode_formula rhs env  in
            (match uu____10930 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10945) ->
                      (l1, decls1)
                  | uu____10950 ->
                      let uu____10951 = encode_formula lhs env  in
                      (match uu____10951 with
                       | (l2,decls2) ->
                           let uu____10962 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10962, (FStar_List.append decls1 decls2)))))
        | uu____10965 -> failwith "impossible"  in
      let mk_ite r uu___90_10986 =
        match uu___90_10986 with
        | (guard,uu____10992)::(_then,uu____10994)::(_else,uu____10996)::[]
            ->
            let uu____11033 = encode_formula guard env  in
            (match uu____11033 with
             | (g,decls1) ->
                 let uu____11044 = encode_formula _then env  in
                 (match uu____11044 with
                  | (t,decls2) ->
                      let uu____11055 = encode_formula _else env  in
                      (match uu____11055 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11069 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11094 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11094  in
      let connectives =
        let uu____11112 =
          let uu____11125 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11125)  in
        let uu____11142 =
          let uu____11157 =
            let uu____11170 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11170)  in
          let uu____11187 =
            let uu____11202 =
              let uu____11217 =
                let uu____11230 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11230)  in
              let uu____11247 =
                let uu____11262 =
                  let uu____11277 =
                    let uu____11290 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11290)  in
                  [uu____11277;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11262  in
              uu____11217 :: uu____11247  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11202  in
          uu____11157 :: uu____11187  in
        uu____11112 :: uu____11142  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11611 = encode_formula phi' env  in
            (match uu____11611 with
             | (phi2,decls) ->
                 let uu____11622 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11622, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11623 ->
            let uu____11630 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11630 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11669 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11669 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11681;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11683;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11685;_}::[]),e2)
            ->
            let uu____11709 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11709 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11756::(x,uu____11758)::(t,uu____11760)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11807 = encode_term x env  in
                 (match uu____11807 with
                  | (x1,decls) ->
                      let uu____11818 = encode_term t env  in
                      (match uu____11818 with
                       | (t1,decls') ->
                           let uu____11829 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11829, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11834)::(msg,uu____11836)::(phi2,uu____11838)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11883 =
                   let uu____11888 =
                     let uu____11889 = FStar_Syntax_Subst.compress r  in
                     uu____11889.FStar_Syntax_Syntax.n  in
                   let uu____11892 =
                     let uu____11893 = FStar_Syntax_Subst.compress msg  in
                     uu____11893.FStar_Syntax_Syntax.n  in
                   (uu____11888, uu____11892)  in
                 (match uu____11883 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11902))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11908 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11915)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11940 when head_redex env head2 ->
                 let uu____11953 = whnf env phi1  in
                 encode_formula uu____11953 env
             | uu____11954 ->
                 let uu____11967 = encode_term phi1 env  in
                 (match uu____11967 with
                  | (tt,decls) ->
                      let uu____11978 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___116_11981 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___116_11981.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___116_11981.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____11978, decls)))
        | uu____11982 ->
            let uu____11983 = encode_term phi1 env  in
            (match uu____11983 with
             | (tt,decls) ->
                 let uu____11994 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___117_11997 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___117_11997.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___117_11997.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____11994, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12033 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12033 with
        | (vars,guards,env2,decls,uu____12072) ->
            let uu____12085 =
              let uu____12098 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12150 =
                          let uu____12161 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12201  ->
                                    match uu____12201 with
                                    | (t,uu____12215) ->
                                        encode_smt_pattern t
                                          (let uu___118_12221 = env2  in
                                           {
                                             bindings =
                                               (uu___118_12221.bindings);
                                             depth = (uu___118_12221.depth);
                                             tcenv = (uu___118_12221.tcenv);
                                             warn = (uu___118_12221.warn);
                                             cache = (uu___118_12221.cache);
                                             nolabels =
                                               (uu___118_12221.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___118_12221.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___118_12221.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12161 FStar_List.unzip
                           in
                        match uu____12150 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12098 FStar_List.unzip  in
            (match uu____12085 with
             | (pats,decls') ->
                 let uu____12330 = encode_formula body env2  in
                 (match uu____12330 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12362;
                             FStar_SMTEncoding_Term.rng = uu____12363;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12378 -> guards  in
                      let uu____12383 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12383, body1,
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
                (fun uu____12443  ->
                   match uu____12443 with
                   | (x,uu____12449) ->
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
               let uu____12457 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12469 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12469) uu____12457 tl1
                in
             let uu____12472 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12499  ->
                       match uu____12499 with
                       | (b,uu____12505) ->
                           let uu____12506 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12506))
                in
             (match uu____12472 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12512) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12526 =
                    let uu____12531 =
                      let uu____12532 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12532
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12531)
                     in
                  FStar_Errors.log_issue pos uu____12526)
          in
       let uu____12533 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12533 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12542 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12600  ->
                     match uu____12600 with
                     | (l,uu____12614) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12542 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12647,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12687 = encode_q_body env vars pats body  in
             match uu____12687 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12732 =
                     let uu____12743 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12743)  in
                   FStar_SMTEncoding_Term.mkForall uu____12732
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12762 = encode_q_body env vars pats body  in
             match uu____12762 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12806 =
                   let uu____12807 =
                     let uu____12818 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12818)  in
                   FStar_SMTEncoding_Term.mkExists uu____12807
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____12806, decls))))

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
  let uu____12921 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____12921 with
  | (asym,a) ->
      let uu____12928 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____12928 with
       | (xsym,x) ->
           let uu____12935 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____12935 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____12983 =
                      let uu____12994 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____12994, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12983  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13020 =
                      let uu____13027 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13027)  in
                    FStar_SMTEncoding_Util.mkApp uu____13020  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13040 =
                    let uu____13043 =
                      let uu____13046 =
                        let uu____13049 =
                          let uu____13050 =
                            let uu____13057 =
                              let uu____13058 =
                                let uu____13069 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13069)  in
                              FStar_SMTEncoding_Util.mkForall uu____13058  in
                            (uu____13057, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13050  in
                        let uu____13086 =
                          let uu____13089 =
                            let uu____13090 =
                              let uu____13097 =
                                let uu____13098 =
                                  let uu____13109 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13109)  in
                                FStar_SMTEncoding_Util.mkForall uu____13098
                                 in
                              (uu____13097,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13090  in
                          [uu____13089]  in
                        uu____13049 :: uu____13086  in
                      xtok_decl :: uu____13046  in
                    xname_decl :: uu____13043  in
                  (xtok1, (FStar_List.length vars), uu____13040)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13206 =
                    let uu____13221 =
                      let uu____13232 =
                        let uu____13233 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13233
                         in
                      quant axy uu____13232  in
                    (FStar_Parser_Const.op_Eq, uu____13221)  in
                  let uu____13244 =
                    let uu____13261 =
                      let uu____13276 =
                        let uu____13287 =
                          let uu____13288 =
                            let uu____13289 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13289  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13288
                           in
                        quant axy uu____13287  in
                      (FStar_Parser_Const.op_notEq, uu____13276)  in
                    let uu____13300 =
                      let uu____13317 =
                        let uu____13332 =
                          let uu____13343 =
                            let uu____13344 =
                              let uu____13345 =
                                let uu____13350 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13351 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13350, uu____13351)  in
                              FStar_SMTEncoding_Util.mkLT uu____13345  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13344
                             in
                          quant xy uu____13343  in
                        (FStar_Parser_Const.op_LT, uu____13332)  in
                      let uu____13362 =
                        let uu____13379 =
                          let uu____13394 =
                            let uu____13405 =
                              let uu____13406 =
                                let uu____13407 =
                                  let uu____13412 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13413 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13412, uu____13413)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13407  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13406
                               in
                            quant xy uu____13405  in
                          (FStar_Parser_Const.op_LTE, uu____13394)  in
                        let uu____13424 =
                          let uu____13441 =
                            let uu____13456 =
                              let uu____13467 =
                                let uu____13468 =
                                  let uu____13469 =
                                    let uu____13474 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13475 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13474, uu____13475)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13469  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13468
                                 in
                              quant xy uu____13467  in
                            (FStar_Parser_Const.op_GT, uu____13456)  in
                          let uu____13486 =
                            let uu____13503 =
                              let uu____13518 =
                                let uu____13529 =
                                  let uu____13530 =
                                    let uu____13531 =
                                      let uu____13536 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13537 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13536, uu____13537)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13531
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13530
                                   in
                                quant xy uu____13529  in
                              (FStar_Parser_Const.op_GTE, uu____13518)  in
                            let uu____13548 =
                              let uu____13565 =
                                let uu____13580 =
                                  let uu____13591 =
                                    let uu____13592 =
                                      let uu____13593 =
                                        let uu____13598 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13599 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13598, uu____13599)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13593
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13592
                                     in
                                  quant xy uu____13591  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13580)
                                 in
                              let uu____13610 =
                                let uu____13627 =
                                  let uu____13642 =
                                    let uu____13653 =
                                      let uu____13654 =
                                        let uu____13655 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13655
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13654
                                       in
                                    quant qx uu____13653  in
                                  (FStar_Parser_Const.op_Minus, uu____13642)
                                   in
                                let uu____13666 =
                                  let uu____13683 =
                                    let uu____13698 =
                                      let uu____13709 =
                                        let uu____13710 =
                                          let uu____13711 =
                                            let uu____13716 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____13717 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____13716, uu____13717)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13711
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13710
                                         in
                                      quant xy uu____13709  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13698)
                                     in
                                  let uu____13728 =
                                    let uu____13745 =
                                      let uu____13760 =
                                        let uu____13771 =
                                          let uu____13772 =
                                            let uu____13773 =
                                              let uu____13778 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____13779 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____13778, uu____13779)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13773
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13772
                                           in
                                        quant xy uu____13771  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13760)
                                       in
                                    let uu____13790 =
                                      let uu____13807 =
                                        let uu____13822 =
                                          let uu____13833 =
                                            let uu____13834 =
                                              let uu____13835 =
                                                let uu____13840 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____13841 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____13840, uu____13841)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13835
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13834
                                             in
                                          quant xy uu____13833  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13822)
                                         in
                                      let uu____13852 =
                                        let uu____13869 =
                                          let uu____13884 =
                                            let uu____13895 =
                                              let uu____13896 =
                                                let uu____13897 =
                                                  let uu____13902 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____13903 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____13902, uu____13903)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13897
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13896
                                               in
                                            quant xy uu____13895  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13884)
                                           in
                                        let uu____13914 =
                                          let uu____13931 =
                                            let uu____13946 =
                                              let uu____13957 =
                                                let uu____13958 =
                                                  let uu____13959 =
                                                    let uu____13964 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____13965 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____13964,
                                                      uu____13965)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13959
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13958
                                                 in
                                              quant xy uu____13957  in
                                            (FStar_Parser_Const.op_And,
                                              uu____13946)
                                             in
                                          let uu____13976 =
                                            let uu____13993 =
                                              let uu____14008 =
                                                let uu____14019 =
                                                  let uu____14020 =
                                                    let uu____14021 =
                                                      let uu____14026 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14027 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14026,
                                                        uu____14027)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14021
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14020
                                                   in
                                                quant xy uu____14019  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14008)
                                               in
                                            let uu____14038 =
                                              let uu____14055 =
                                                let uu____14070 =
                                                  let uu____14081 =
                                                    let uu____14082 =
                                                      let uu____14083 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14083
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14082
                                                     in
                                                  quant qx uu____14081  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14070)
                                                 in
                                              [uu____14055]  in
                                            uu____13993 :: uu____14038  in
                                          uu____13931 :: uu____13976  in
                                        uu____13869 :: uu____13914  in
                                      uu____13807 :: uu____13852  in
                                    uu____13745 :: uu____13790  in
                                  uu____13683 :: uu____13728  in
                                uu____13627 :: uu____13666  in
                              uu____13565 :: uu____13610  in
                            uu____13503 :: uu____13548  in
                          uu____13441 :: uu____13486  in
                        uu____13379 :: uu____13424  in
                      uu____13317 :: uu____13362  in
                    uu____13261 :: uu____13300  in
                  uu____13206 :: uu____13244  in
                let mk1 l v1 =
                  let uu____14333 =
                    let uu____14344 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14410  ->
                              match uu____14410 with
                              | (l',uu____14426) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14344
                      (FStar_Option.map
                         (fun uu____14498  ->
                            match uu____14498 with | (uu____14521,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14333 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14606  ->
                          match uu____14606 with
                          | (l',uu____14622) -> FStar_Ident.lid_equals l l'))
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
        let uu____14664 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14664 with
        | (xxsym,xx) ->
            let uu____14671 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14671 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14681 =
                   let uu____14688 =
                     let uu____14689 =
                       let uu____14700 =
                         let uu____14701 =
                           let uu____14706 =
                             let uu____14707 =
                               let uu____14712 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14712)  in
                             FStar_SMTEncoding_Util.mkEq uu____14707  in
                           (xx_has_type, uu____14706)  in
                         FStar_SMTEncoding_Util.mkImp uu____14701  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14700)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14689  in
                   let uu____14737 =
                     let uu____14738 =
                       let uu____14739 =
                         let uu____14740 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14740  in
                       Prims.strcat module_name uu____14739  in
                     varops.mk_unique uu____14738  in
                   (uu____14688, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14737)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14681)
  
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
    let uu____14776 =
      let uu____14777 =
        let uu____14784 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14784, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14777  in
    let uu____14787 =
      let uu____14790 =
        let uu____14791 =
          let uu____14798 =
            let uu____14799 =
              let uu____14810 =
                let uu____14811 =
                  let uu____14816 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____14816)  in
                FStar_SMTEncoding_Util.mkImp uu____14811  in
              ([[typing_pred]], [xx], uu____14810)  in
            mkForall_fuel uu____14799  in
          (uu____14798, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14791  in
      [uu____14790]  in
    uu____14776 :: uu____14787  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____14858 =
      let uu____14859 =
        let uu____14866 =
          let uu____14867 =
            let uu____14878 =
              let uu____14883 =
                let uu____14886 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____14886]  in
              [uu____14883]  in
            let uu____14891 =
              let uu____14892 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14892 tt  in
            (uu____14878, [bb], uu____14891)  in
          FStar_SMTEncoding_Util.mkForall uu____14867  in
        (uu____14866, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14859  in
    let uu____14913 =
      let uu____14916 =
        let uu____14917 =
          let uu____14924 =
            let uu____14925 =
              let uu____14936 =
                let uu____14937 =
                  let uu____14942 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____14942)  in
                FStar_SMTEncoding_Util.mkImp uu____14937  in
              ([[typing_pred]], [xx], uu____14936)  in
            mkForall_fuel uu____14925  in
          (uu____14924, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14917  in
      [uu____14916]  in
    uu____14858 :: uu____14913  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____14992 =
        let uu____14993 =
          let uu____15000 =
            let uu____15003 =
              let uu____15006 =
                let uu____15009 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15010 =
                  let uu____15013 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15013]  in
                uu____15009 :: uu____15010  in
              tt :: uu____15006  in
            tt :: uu____15003  in
          ("Prims.Precedes", uu____15000)  in
        FStar_SMTEncoding_Util.mkApp uu____14993  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14992  in
    let precedes_y_x =
      let uu____15017 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15017  in
    let uu____15020 =
      let uu____15021 =
        let uu____15028 =
          let uu____15029 =
            let uu____15040 =
              let uu____15045 =
                let uu____15048 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15048]  in
              [uu____15045]  in
            let uu____15053 =
              let uu____15054 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15054 tt  in
            (uu____15040, [bb], uu____15053)  in
          FStar_SMTEncoding_Util.mkForall uu____15029  in
        (uu____15028, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15021  in
    let uu____15075 =
      let uu____15078 =
        let uu____15079 =
          let uu____15086 =
            let uu____15087 =
              let uu____15098 =
                let uu____15099 =
                  let uu____15104 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15104)  in
                FStar_SMTEncoding_Util.mkImp uu____15099  in
              ([[typing_pred]], [xx], uu____15098)  in
            mkForall_fuel uu____15087  in
          (uu____15086, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15079  in
      let uu____15129 =
        let uu____15132 =
          let uu____15133 =
            let uu____15140 =
              let uu____15141 =
                let uu____15152 =
                  let uu____15153 =
                    let uu____15158 =
                      let uu____15159 =
                        let uu____15162 =
                          let uu____15165 =
                            let uu____15168 =
                              let uu____15169 =
                                let uu____15174 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15175 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15174, uu____15175)  in
                              FStar_SMTEncoding_Util.mkGT uu____15169  in
                            let uu____15176 =
                              let uu____15179 =
                                let uu____15180 =
                                  let uu____15185 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15186 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15185, uu____15186)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15180  in
                              let uu____15187 =
                                let uu____15190 =
                                  let uu____15191 =
                                    let uu____15196 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15197 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15196, uu____15197)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15191  in
                                [uu____15190]  in
                              uu____15179 :: uu____15187  in
                            uu____15168 :: uu____15176  in
                          typing_pred_y :: uu____15165  in
                        typing_pred :: uu____15162  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15159  in
                    (uu____15158, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15153  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15152)
                 in
              mkForall_fuel uu____15141  in
            (uu____15140,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15133  in
        [uu____15132]  in
      uu____15078 :: uu____15129  in
    uu____15020 :: uu____15075  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15243 =
      let uu____15244 =
        let uu____15251 =
          let uu____15252 =
            let uu____15263 =
              let uu____15268 =
                let uu____15271 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15271]  in
              [uu____15268]  in
            let uu____15276 =
              let uu____15277 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15277 tt  in
            (uu____15263, [bb], uu____15276)  in
          FStar_SMTEncoding_Util.mkForall uu____15252  in
        (uu____15251, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15244  in
    let uu____15298 =
      let uu____15301 =
        let uu____15302 =
          let uu____15309 =
            let uu____15310 =
              let uu____15321 =
                let uu____15322 =
                  let uu____15327 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15327)  in
                FStar_SMTEncoding_Util.mkImp uu____15322  in
              ([[typing_pred]], [xx], uu____15321)  in
            mkForall_fuel uu____15310  in
          (uu____15309, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15302  in
      [uu____15301]  in
    uu____15243 :: uu____15298  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15380 =
      let uu____15381 =
        let uu____15388 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15388, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15381  in
    [uu____15380]  in
  let mk_and_interp env conj uu____15400 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15425 =
      let uu____15426 =
        let uu____15433 =
          let uu____15434 =
            let uu____15445 =
              let uu____15446 =
                let uu____15451 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15451, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15446  in
            ([[l_and_a_b]], [aa; bb], uu____15445)  in
          FStar_SMTEncoding_Util.mkForall uu____15434  in
        (uu____15433, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15426  in
    [uu____15425]  in
  let mk_or_interp env disj uu____15489 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15514 =
      let uu____15515 =
        let uu____15522 =
          let uu____15523 =
            let uu____15534 =
              let uu____15535 =
                let uu____15540 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15540, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15535  in
            ([[l_or_a_b]], [aa; bb], uu____15534)  in
          FStar_SMTEncoding_Util.mkForall uu____15523  in
        (uu____15522, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15515  in
    [uu____15514]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15603 =
      let uu____15604 =
        let uu____15611 =
          let uu____15612 =
            let uu____15623 =
              let uu____15624 =
                let uu____15629 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15629, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15624  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15623)  in
          FStar_SMTEncoding_Util.mkForall uu____15612  in
        (uu____15611, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15604  in
    [uu____15603]  in
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
    let uu____15702 =
      let uu____15703 =
        let uu____15710 =
          let uu____15711 =
            let uu____15722 =
              let uu____15723 =
                let uu____15728 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15728, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15723  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15722)  in
          FStar_SMTEncoding_Util.mkForall uu____15711  in
        (uu____15710, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15703  in
    [uu____15702]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15799 =
      let uu____15800 =
        let uu____15807 =
          let uu____15808 =
            let uu____15819 =
              let uu____15820 =
                let uu____15825 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____15825, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15820  in
            ([[l_imp_a_b]], [aa; bb], uu____15819)  in
          FStar_SMTEncoding_Util.mkForall uu____15808  in
        (uu____15807, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15800  in
    [uu____15799]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15888 =
      let uu____15889 =
        let uu____15896 =
          let uu____15897 =
            let uu____15908 =
              let uu____15909 =
                let uu____15914 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____15914, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15909  in
            ([[l_iff_a_b]], [aa; bb], uu____15908)  in
          FStar_SMTEncoding_Util.mkForall uu____15897  in
        (uu____15896, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15889  in
    [uu____15888]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____15966 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15966  in
    let uu____15969 =
      let uu____15970 =
        let uu____15977 =
          let uu____15978 =
            let uu____15989 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____15989)  in
          FStar_SMTEncoding_Util.mkForall uu____15978  in
        (uu____15977, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15970  in
    [uu____15969]  in
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
      let uu____16049 =
        let uu____16056 =
          let uu____16059 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16059]  in
        ("Valid", uu____16056)  in
      FStar_SMTEncoding_Util.mkApp uu____16049  in
    let uu____16062 =
      let uu____16063 =
        let uu____16070 =
          let uu____16071 =
            let uu____16082 =
              let uu____16083 =
                let uu____16088 =
                  let uu____16089 =
                    let uu____16100 =
                      let uu____16105 =
                        let uu____16108 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16108]  in
                      [uu____16105]  in
                    let uu____16113 =
                      let uu____16114 =
                        let uu____16119 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16119, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16114  in
                    (uu____16100, [xx1], uu____16113)  in
                  FStar_SMTEncoding_Util.mkForall uu____16089  in
                (uu____16088, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16083  in
            ([[l_forall_a_b]], [aa; bb], uu____16082)  in
          FStar_SMTEncoding_Util.mkForall uu____16071  in
        (uu____16070, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16063  in
    [uu____16062]  in
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
      let uu____16201 =
        let uu____16208 =
          let uu____16211 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16211]  in
        ("Valid", uu____16208)  in
      FStar_SMTEncoding_Util.mkApp uu____16201  in
    let uu____16214 =
      let uu____16215 =
        let uu____16222 =
          let uu____16223 =
            let uu____16234 =
              let uu____16235 =
                let uu____16240 =
                  let uu____16241 =
                    let uu____16252 =
                      let uu____16257 =
                        let uu____16260 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16260]  in
                      [uu____16257]  in
                    let uu____16265 =
                      let uu____16266 =
                        let uu____16271 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16271, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16266  in
                    (uu____16252, [xx1], uu____16265)  in
                  FStar_SMTEncoding_Util.mkExists uu____16241  in
                (uu____16240, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16235  in
            ([[l_exists_a_b]], [aa; bb], uu____16234)  in
          FStar_SMTEncoding_Util.mkForall uu____16223  in
        (uu____16222, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16215  in
    [uu____16214]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16331 =
      let uu____16332 =
        let uu____16339 =
          let uu____16340 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16340 range_ty  in
        let uu____16341 = varops.mk_unique "typing_range_const"  in
        (uu____16339, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16341)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16332  in
    [uu____16331]  in
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
        let uu____16375 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16375 x1 t  in
      let uu____16376 =
        let uu____16387 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16387)  in
      FStar_SMTEncoding_Util.mkForall uu____16376  in
    let uu____16410 =
      let uu____16411 =
        let uu____16418 =
          let uu____16419 =
            let uu____16430 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16430)  in
          FStar_SMTEncoding_Util.mkForall uu____16419  in
        (uu____16418,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16411  in
    [uu____16410]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____16480 =
      let uu____16481 =
        let uu____16488 =
          let uu____16489 =
            let uu____16504 =
              let uu____16505 =
                let uu____16510 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____16511 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____16510, uu____16511)  in
              FStar_SMTEncoding_Util.mkAnd uu____16505  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16504)
             in
          FStar_SMTEncoding_Util.mkForall' uu____16489  in
        (uu____16488,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16481  in
    [uu____16480]  in
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
          let uu____16857 =
            FStar_Util.find_opt
              (fun uu____16883  ->
                 match uu____16883 with
                 | (l,uu____16895) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16857 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16920,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16956 = encode_function_type_as_formula t env  in
        match uu____16956 with
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
              let uu____16996 =
                ((let uu____16999 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____16999) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____16996
              then
                let arg_sorts =
                  let uu____17009 =
                    let uu____17010 = FStar_Syntax_Subst.compress t_norm  in
                    uu____17010.FStar_Syntax_Syntax.n  in
                  match uu____17009 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17016) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____17046  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____17051 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____17053 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____17053 with
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
                (let uu____17086 = prims.is lid  in
                 if uu____17086
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17094 = prims.mk lid vname  in
                   match uu____17094 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17121 =
                      let uu____17132 = curried_arrow_formals_comp t_norm  in
                      match uu____17132 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17150 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17150
                            then
                              let uu____17151 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___119_17154 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___119_17154.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___119_17154.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___119_17154.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___119_17154.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___119_17154.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___119_17154.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___119_17154.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___119_17154.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___119_17154.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___119_17154.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___119_17154.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___119_17154.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___119_17154.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___119_17154.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___119_17154.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___119_17154.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___119_17154.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___119_17154.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___119_17154.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___119_17154.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___119_17154.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___119_17154.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___119_17154.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___119_17154.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___119_17154.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___119_17154.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___119_17154.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___119_17154.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___119_17154.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___119_17154.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___119_17154.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___119_17154.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___119_17154.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___119_17154.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17151
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17166 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17166)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17121 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____17216 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____17216 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17241 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___91_17283  ->
                                       match uu___91_17283 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17287 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17287 with
                                            | (uu____17308,(xxsym,uu____17310))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17328 =
                                                  let uu____17329 =
                                                    let uu____17336 =
                                                      let uu____17337 =
                                                        let uu____17348 =
                                                          let uu____17349 =
                                                            let uu____17354 =
                                                              let uu____17355
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17355
                                                               in
                                                            (vapp,
                                                              uu____17354)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17349
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17348)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17337
                                                       in
                                                    (uu____17336,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17329
                                                   in
                                                [uu____17328])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17374 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17374 with
                                            | (uu____17395,(xxsym,uu____17397))
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
                                                let uu____17420 =
                                                  let uu____17421 =
                                                    let uu____17428 =
                                                      let uu____17429 =
                                                        let uu____17440 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17440)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17429
                                                       in
                                                    (uu____17428,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17421
                                                   in
                                                [uu____17420])
                                       | uu____17457 -> []))
                                in
                             let uu____17458 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17458 with
                              | (vars,guards,env',decls1,uu____17485) ->
                                  let uu____17498 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17507 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17507, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17509 =
                                          encode_formula p env'  in
                                        (match uu____17509 with
                                         | (g,ds) ->
                                             let uu____17520 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17520,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17498 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17533 =
                                           let uu____17540 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17540)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17533
                                          in
                                       let uu____17549 =
                                         let vname_decl =
                                           let uu____17557 =
                                             let uu____17568 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17578  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17568,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17557
                                            in
                                         let uu____17587 =
                                           let env2 =
                                             let uu___120_17593 = env1  in
                                             {
                                               bindings =
                                                 (uu___120_17593.bindings);
                                               depth = (uu___120_17593.depth);
                                               tcenv = (uu___120_17593.tcenv);
                                               warn = (uu___120_17593.warn);
                                               cache = (uu___120_17593.cache);
                                               nolabels =
                                                 (uu___120_17593.nolabels);
                                               use_zfuel_name =
                                                 (uu___120_17593.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___120_17593.current_module_name)
                                             }  in
                                           let uu____17594 =
                                             let uu____17595 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17595
                                              in
                                           if uu____17594
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17587 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17610::uu____17611 ->
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
                                                     let uu____17651 =
                                                       let uu____17662 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17662)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17651
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17689 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17692 =
                                               match formals with
                                               | [] ->
                                                   let uu____17709 =
                                                     let uu____17710 =
                                                       let uu____17713 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17713
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____17710
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17709)
                                               | uu____17722 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17729 =
                                                       let uu____17736 =
                                                         let uu____17737 =
                                                           let uu____17748 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17748)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17737
                                                          in
                                                       (uu____17736,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17729
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17692 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17549 with
                                        | (decls2,env2) ->
                                            let uu____17791 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17799 =
                                                encode_term res_t1 env'  in
                                              match uu____17799 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17812 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17812, decls)
                                               in
                                            (match uu____17791 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17823 =
                                                     let uu____17830 =
                                                       let uu____17831 =
                                                         let uu____17842 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17842)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17831
                                                        in
                                                     (uu____17830,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17823
                                                    in
                                                 let freshness =
                                                   let uu____17858 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17858
                                                   then
                                                     let uu____17863 =
                                                       let uu____17864 =
                                                         let uu____17875 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17886 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17875,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17886)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17864
                                                        in
                                                     let uu____17889 =
                                                       let uu____17892 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17892]  in
                                                     uu____17863 ::
                                                       uu____17889
                                                   else []  in
                                                 let g =
                                                   let uu____17897 =
                                                     let uu____17900 =
                                                       let uu____17903 =
                                                         let uu____17906 =
                                                           let uu____17909 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17909
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17906
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17903
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17900
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17897
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
          let uu____17934 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____17934 with
          | FStar_Pervasives_Native.None  ->
              let uu____17945 = encode_free_var false env x t t_norm []  in
              (match uu____17945 with
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
            let uu____17998 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____17998 with
            | (decls,env1) ->
                let uu____18017 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18017
                then
                  let uu____18024 =
                    let uu____18027 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18027  in
                  (uu____18024, env1)
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
             (fun uu____18079  ->
                fun lb  ->
                  match uu____18079 with
                  | (decls,env1) ->
                      let uu____18099 =
                        let uu____18106 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18106
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18099 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18127 = FStar_Syntax_Util.head_and_args t  in
    match uu____18127 with
    | (hd1,args) ->
        let uu____18164 =
          let uu____18165 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18165.FStar_Syntax_Syntax.n  in
        (match uu____18164 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18169,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18188 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18210  ->
      fun quals  ->
        match uu____18210 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18286 = FStar_Util.first_N nbinders formals  in
              match uu____18286 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18367  ->
                         fun uu____18368  ->
                           match (uu____18367, uu____18368) with
                           | ((formal,uu____18386),(binder,uu____18388)) ->
                               let uu____18397 =
                                 let uu____18404 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18404)  in
                               FStar_Syntax_Syntax.NT uu____18397) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18412 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18443  ->
                              match uu____18443 with
                              | (x,i) ->
                                  let uu____18454 =
                                    let uu___121_18455 = x  in
                                    let uu____18456 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_18455.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_18455.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18456
                                    }  in
                                  (uu____18454, i)))
                       in
                    FStar_All.pipe_right uu____18412
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18474 =
                      let uu____18475 = FStar_Syntax_Subst.compress body  in
                      let uu____18476 =
                        let uu____18477 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18477
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18475
                        uu____18476
                       in
                    uu____18474 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18538 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18538
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___122_18541 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_18541.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_18541.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_18541.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_18541.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_18541.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_18541.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_18541.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_18541.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_18541.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_18541.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_18541.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_18541.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_18541.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_18541.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_18541.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_18541.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_18541.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_18541.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_18541.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___122_18541.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___122_18541.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___122_18541.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_18541.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_18541.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___122_18541.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_18541.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_18541.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___122_18541.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___122_18541.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_18541.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___122_18541.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___122_18541.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___122_18541.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___122_18541.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18574 = FStar_Syntax_Util.abs_formals e  in
                match uu____18574 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18638::uu____18639 ->
                         let uu____18654 =
                           let uu____18655 =
                             let uu____18658 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18658
                              in
                           uu____18655.FStar_Syntax_Syntax.n  in
                         (match uu____18654 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18701 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18701 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18743 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18743
                                   then
                                     let uu____18778 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18778 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18872  ->
                                                   fun uu____18873  ->
                                                     match (uu____18872,
                                                             uu____18873)
                                                     with
                                                     | ((x,uu____18891),
                                                        (b,uu____18893)) ->
                                                         let uu____18902 =
                                                           let uu____18909 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____18909)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18902)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____18911 =
                                            let uu____18932 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____18932)
                                             in
                                          (uu____18911, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19000 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19000 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19089) ->
                              let uu____19094 =
                                let uu____19115 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19115  in
                              (uu____19094, true)
                          | uu____19180 when Prims.op_Negation norm1 ->
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
                          | uu____19182 ->
                              let uu____19183 =
                                let uu____19184 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19185 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19184
                                  uu____19185
                                 in
                              failwith uu____19183)
                     | uu____19210 ->
                         let rec aux' t_norm2 =
                           let uu____19235 =
                             let uu____19236 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19236.FStar_Syntax_Syntax.n  in
                           match uu____19235 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19277 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19277 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19305 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19305 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19385)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19390 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19446 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19446
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19458 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19521  ->
                            fun lb  ->
                              match uu____19521 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19576 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19576
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19579 =
                                      let uu____19588 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19588
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19579 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19458 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____19703 =
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
                        | uu____19709 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19717 = mk_fv ()  in
                                   mk_Apply uu____19717 vars)
                            else
                              (let uu____19719 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____19719)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19771;
                             FStar_Syntax_Syntax.lbeff = uu____19772;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____19774;_}::[],t_norm::[],fvb::[])
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
                                       ((let uu___125_19856 = env2  in
                                         {
                                           bindings =
                                             (uu___125_19856.bindings);
                                           depth = (uu___125_19856.depth);
                                           tcenv = tcenv';
                                           warn = (uu___125_19856.warn);
                                           cache = (uu___125_19856.cache);
                                           nolabels =
                                             (uu___125_19856.nolabels);
                                           use_zfuel_name =
                                             (uu___125_19856.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___125_19856.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___125_19856.current_module_name)
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
                                                  uu____20362;_})
                                  ->
                                  let uu____20383 =
                                    let uu____20390 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____20390 with
                                    | (tcenv',uu____20412,e_t) ->
                                        let uu____20418 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20429 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____20418 with
                                         | (e1,t_norm1) ->
                                             ((let uu___126_20445 = env3  in
                                               {
                                                 bindings =
                                                   (uu___126_20445.bindings);
                                                 depth =
                                                   (uu___126_20445.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___126_20445.warn);
                                                 cache =
                                                   (uu___126_20445.cache);
                                                 nolabels =
                                                   (uu___126_20445.nolabels);
                                                 use_zfuel_name =
                                                   (uu___126_20445.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___126_20445.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___126_20445.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____20383 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20460 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____20460
                                         then
                                           let uu____20461 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____20462 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____20463 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20461 uu____20462
                                             uu____20463
                                         else ());
                                        (let uu____20465 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____20465 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20502 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____20502
                                               then
                                                 let uu____20503 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____20504 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____20505 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____20506 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20503 uu____20504
                                                   uu____20505 uu____20506
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20510 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____20510 with
                                               | (vars,guards,env'1,binder_decls,uu____20541)
                                                   ->
                                                   let decl_g =
                                                     let uu____20555 =
                                                       let uu____20566 =
                                                         let uu____20569 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20569
                                                          in
                                                       (g, uu____20566,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20555
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
                                                     let uu____20594 =
                                                       let uu____20601 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____20601)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20594
                                                      in
                                                   let gsapp =
                                                     let uu____20611 =
                                                       let uu____20618 =
                                                         let uu____20621 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____20621 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20618)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20611
                                                      in
                                                   let gmax =
                                                     let uu____20627 =
                                                       let uu____20634 =
                                                         let uu____20637 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____20637 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20634)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20627
                                                      in
                                                   let body1 =
                                                     let uu____20643 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____20643
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____20645 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____20645 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____20663 =
                                                            let uu____20670 =
                                                              let uu____20671
                                                                =
                                                                let uu____20686
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
                                                                  uu____20686)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20671
                                                               in
                                                            let uu____20707 =
                                                              let uu____20710
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20710
                                                               in
                                                            (uu____20670,
                                                              uu____20707,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20663
                                                           in
                                                        let eqn_f =
                                                          let uu____20714 =
                                                            let uu____20721 =
                                                              let uu____20722
                                                                =
                                                                let uu____20733
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20733)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20722
                                                               in
                                                            (uu____20721,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20714
                                                           in
                                                        let eqn_g' =
                                                          let uu____20747 =
                                                            let uu____20754 =
                                                              let uu____20755
                                                                =
                                                                let uu____20766
                                                                  =
                                                                  let uu____20767
                                                                    =
                                                                    let uu____20772
                                                                    =
                                                                    let uu____20773
                                                                    =
                                                                    let uu____20780
                                                                    =
                                                                    let uu____20783
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____20783
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____20780)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20773
                                                                     in
                                                                    (gsapp,
                                                                    uu____20772)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____20767
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20766)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20755
                                                               in
                                                            (uu____20754,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20747
                                                           in
                                                        let uu____20806 =
                                                          let uu____20815 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____20815
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____20844)
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
                                                                  let uu____20869
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____20869
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____20874
                                                                  =
                                                                  let uu____20881
                                                                    =
                                                                    let uu____20882
                                                                    =
                                                                    let uu____20893
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20893)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20882
                                                                     in
                                                                  (uu____20881,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____20874
                                                                 in
                                                              let uu____20914
                                                                =
                                                                let uu____20921
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____20921
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____20934
                                                                    =
                                                                    let uu____20937
                                                                    =
                                                                    let uu____20938
                                                                    =
                                                                    let uu____20945
                                                                    =
                                                                    let uu____20946
                                                                    =
                                                                    let uu____20957
                                                                    =
                                                                    let uu____20958
                                                                    =
                                                                    let uu____20963
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____20963,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____20958
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20957)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20946
                                                                     in
                                                                    (uu____20945,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20938
                                                                     in
                                                                    [uu____20937]
                                                                     in
                                                                    (d3,
                                                                    uu____20934)
                                                                 in
                                                              (match uu____20914
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
                                                        (match uu____20806
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
                            let uu____21028 =
                              let uu____21041 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21102  ->
                                   fun uu____21103  ->
                                     match (uu____21102, uu____21103) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21228 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21228 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21041
                               in
                            (match uu____21028 with
                             | (decls2,eqns,env01) ->
                                 let uu____21301 =
                                   let isDeclFun uu___92_21313 =
                                     match uu___92_21313 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21314 -> true
                                     | uu____21325 -> false  in
                                   let uu____21326 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____21326
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____21301 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____21366 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___93_21370  ->
                                 match uu___93_21370 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21371 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21377 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21377)))
                         in
                      if uu____21366
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
                   let uu____21429 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____21429
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
        let uu____21478 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____21478 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____21482 = encode_sigelt' env se  in
      match uu____21482 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21498 =
                  let uu____21499 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____21499  in
                [uu____21498]
            | uu____21500 ->
                let uu____21501 =
                  let uu____21504 =
                    let uu____21505 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21505  in
                  uu____21504 :: g  in
                let uu____21506 =
                  let uu____21509 =
                    let uu____21510 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21510  in
                  [uu____21509]  in
                FStar_List.append uu____21501 uu____21506
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
        let uu____21523 =
          let uu____21524 = FStar_Syntax_Subst.compress t  in
          uu____21524.FStar_Syntax_Syntax.n  in
        match uu____21523 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21528)) -> s = "opaque_to_smt"
        | uu____21529 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____21534 =
          let uu____21535 = FStar_Syntax_Subst.compress t  in
          uu____21535.FStar_Syntax_Syntax.n  in
        match uu____21534 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21539)) -> s = "uninterpreted_by_smt"
        | uu____21540 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21545 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21550 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21553 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21556 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21571 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21575 =
            let uu____21576 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____21576 Prims.op_Negation  in
          if uu____21575
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____21602 ->
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
               let uu____21622 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____21622 with
               | (formals,uu____21640) ->
                   let arity = FStar_List.length formals  in
                   let uu____21658 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____21658 with
                    | (aname,atok,env2) ->
                        let uu____21678 =
                          let uu____21683 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____21683 env2  in
                        (match uu____21678 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____21695 =
                                 let uu____21696 =
                                   let uu____21707 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21723  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____21707,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____21696
                                  in
                               [uu____21695;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____21736 =
                               let aux uu____21788 uu____21789 =
                                 match (uu____21788, uu____21789) with
                                 | ((bv,uu____21841),(env3,acc_sorts,acc)) ->
                                     let uu____21879 = gen_term_var env3 bv
                                        in
                                     (match uu____21879 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____21736 with
                              | (uu____21951,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____21974 =
                                      let uu____21981 =
                                        let uu____21982 =
                                          let uu____21993 =
                                            let uu____21994 =
                                              let uu____21999 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____21999)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____21994
                                             in
                                          ([[app]], xs_sorts, uu____21993)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____21982
                                         in
                                      (uu____21981,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____21974
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____22019 =
                                      let uu____22026 =
                                        let uu____22027 =
                                          let uu____22038 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____22038)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22027
                                         in
                                      (uu____22026,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22019
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____22057 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____22057 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22085,uu____22086)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22087 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____22087 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22104,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22110 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___94_22114  ->
                      match uu___94_22114 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22115 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22120 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22121 -> false))
               in
            Prims.op_Negation uu____22110  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22130 =
               let uu____22137 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22137 env fv t quals  in
             match uu____22130 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22152 =
                   let uu____22155 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22155  in
                 (uu____22152, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22163 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22163 with
           | (uu____22172,f1) ->
               let uu____22174 = encode_formula f1 env  in
               (match uu____22174 with
                | (f2,decls) ->
                    let g =
                      let uu____22188 =
                        let uu____22189 =
                          let uu____22196 =
                            let uu____22199 =
                              let uu____22200 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22200
                               in
                            FStar_Pervasives_Native.Some uu____22199  in
                          let uu____22201 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22196, uu____22201)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22189  in
                      [uu____22188]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22207) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22219 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22237 =
                       let uu____22240 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22240.FStar_Syntax_Syntax.fv_name  in
                     uu____22237.FStar_Syntax_Syntax.v  in
                   let uu____22241 =
                     let uu____22242 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22242  in
                   if uu____22241
                   then
                     let val_decl =
                       let uu___129_22270 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___129_22270.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___129_22270.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___129_22270.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____22275 = encode_sigelt' env1 val_decl  in
                     match uu____22275 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22219 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22303,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22305;
                          FStar_Syntax_Syntax.lbtyp = uu____22306;
                          FStar_Syntax_Syntax.lbeff = uu____22307;
                          FStar_Syntax_Syntax.lbdef = uu____22308;
                          FStar_Syntax_Syntax.lbattrs = uu____22309;_}::[]),uu____22310)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22333 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____22333 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____22362 =
                   let uu____22365 =
                     let uu____22366 =
                       let uu____22373 =
                         let uu____22374 =
                           let uu____22385 =
                             let uu____22386 =
                               let uu____22391 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____22391)  in
                             FStar_SMTEncoding_Util.mkEq uu____22386  in
                           ([[b2t_x]], [xx], uu____22385)  in
                         FStar_SMTEncoding_Util.mkForall uu____22374  in
                       (uu____22373,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____22366  in
                   [uu____22365]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22362
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22424,uu____22425) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_22434  ->
                  match uu___95_22434 with
                  | FStar_Syntax_Syntax.Discriminator uu____22435 -> true
                  | uu____22436 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22439,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22450 =
                     let uu____22451 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____22451.FStar_Ident.idText  in
                   uu____22450 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___96_22455  ->
                     match uu___96_22455 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22456 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22460) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_22477  ->
                  match uu___97_22477 with
                  | FStar_Syntax_Syntax.Projector uu____22478 -> true
                  | uu____22483 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____22486 = try_lookup_free_var env l  in
          (match uu____22486 with
           | FStar_Pervasives_Native.Some uu____22493 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___130_22497 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___130_22497.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___130_22497.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___130_22497.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22504) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22522) ->
          let uu____22531 = encode_sigelts env ses  in
          (match uu____22531 with
           | (g,env1) ->
               let uu____22548 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___98_22571  ->
                         match uu___98_22571 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22572;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22573;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22574;_}
                             -> false
                         | uu____22577 -> true))
                  in
               (match uu____22548 with
                | (g',inversions) ->
                    let uu____22592 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___99_22613  ->
                              match uu___99_22613 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22614 ->
                                  true
                              | uu____22625 -> false))
                       in
                    (match uu____22592 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22643,tps,k,uu____22646,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___100_22663  ->
                    match uu___100_22663 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22664 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22673 = c  in
              match uu____22673 with
              | (name,args,uu____22678,uu____22679,uu____22680) ->
                  let uu____22685 =
                    let uu____22686 =
                      let uu____22697 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22714  ->
                                match uu____22714 with
                                | (uu____22721,sort,uu____22723) -> sort))
                         in
                      (name, uu____22697, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____22686  in
                  [uu____22685]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____22750 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____22756 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____22756 FStar_Option.isNone))
               in
            if uu____22750
            then []
            else
              (let uu____22788 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____22788 with
               | (xxsym,xx) ->
                   let uu____22797 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____22836  ->
                             fun l  ->
                               match uu____22836 with
                               | (out,decls) ->
                                   let uu____22856 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____22856 with
                                    | (uu____22867,data_t) ->
                                        let uu____22869 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____22869 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____22915 =
                                                 let uu____22916 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____22916.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____22915 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____22927,indices) ->
                                                   indices
                                               | uu____22949 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____22973  ->
                                                         match uu____22973
                                                         with
                                                         | (x,uu____22979) ->
                                                             let uu____22980
                                                               =
                                                               let uu____22981
                                                                 =
                                                                 let uu____22988
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____22988,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____22981
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____22980)
                                                    env)
                                                in
                                             let uu____22991 =
                                               encode_args indices env1  in
                                             (match uu____22991 with
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
                                                      let uu____23017 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23033
                                                                 =
                                                                 let uu____23038
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23038,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23033)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23017
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23041 =
                                                      let uu____23042 =
                                                        let uu____23047 =
                                                          let uu____23048 =
                                                            let uu____23053 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23053,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23048
                                                           in
                                                        (out, uu____23047)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23042
                                                       in
                                                    (uu____23041,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____22797 with
                    | (data_ax,decls) ->
                        let uu____23066 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23066 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23077 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23077 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23081 =
                                 let uu____23088 =
                                   let uu____23089 =
                                     let uu____23100 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23115 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23100,
                                       uu____23115)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23089
                                    in
                                 let uu____23130 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23088,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23130)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23081
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23133 =
            let uu____23146 =
              let uu____23147 = FStar_Syntax_Subst.compress k  in
              uu____23147.FStar_Syntax_Syntax.n  in
            match uu____23146 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23192 -> (tps, k)  in
          (match uu____23133 with
           | (formals,res) ->
               let uu____23215 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23215 with
                | (formals1,res1) ->
                    let uu____23226 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23226 with
                     | (vars,guards,env',binder_decls,uu____23251) ->
                         let arity = FStar_List.length vars  in
                         let uu____23265 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____23265 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23288 =
                                  let uu____23295 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23295)  in
                                FStar_SMTEncoding_Util.mkApp uu____23288  in
                              let uu____23304 =
                                let tname_decl =
                                  let uu____23314 =
                                    let uu____23315 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23347  ->
                                              match uu____23347 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23360 = varops.next_id ()  in
                                    (tname, uu____23315,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23360, false)
                                     in
                                  constructor_or_logic_type_decl uu____23314
                                   in
                                let uu____23369 =
                                  match vars with
                                  | [] ->
                                      let uu____23382 =
                                        let uu____23383 =
                                          let uu____23386 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23386
                                           in
                                        push_free_var env1 t arity tname
                                          uu____23383
                                         in
                                      ([], uu____23382)
                                  | uu____23397 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____23406 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23406
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____23420 =
                                          let uu____23427 =
                                            let uu____23428 =
                                              let uu____23443 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23443)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23428
                                             in
                                          (uu____23427,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23420
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____23369 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23304 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23483 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____23483 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23501 =
                                               let uu____23502 =
                                                 let uu____23509 =
                                                   let uu____23510 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23510
                                                    in
                                                 (uu____23509,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23502
                                                in
                                             [uu____23501]
                                           else []  in
                                         let uu____23514 =
                                           let uu____23517 =
                                             let uu____23520 =
                                               let uu____23521 =
                                                 let uu____23528 =
                                                   let uu____23529 =
                                                     let uu____23540 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____23540)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23529
                                                    in
                                                 (uu____23528,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23521
                                                in
                                             [uu____23520]  in
                                           FStar_List.append karr uu____23517
                                            in
                                         FStar_List.append decls1 uu____23514
                                      in
                                   let aux =
                                     let uu____23556 =
                                       let uu____23559 =
                                         inversion_axioms tapp vars  in
                                       let uu____23562 =
                                         let uu____23565 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____23565]  in
                                       FStar_List.append uu____23559
                                         uu____23562
                                        in
                                     FStar_List.append kindingAx uu____23556
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23572,uu____23573,uu____23574,uu____23575,uu____23576)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23584,t,uu____23586,n_tps,uu____23588) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____23596 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____23596 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____23636 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____23636 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____23657 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____23657 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____23671 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____23671 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____23741 =
                                            mk_term_projector_name d x  in
                                          (uu____23741,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____23743 =
                                  let uu____23762 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23762, true)
                                   in
                                FStar_All.pipe_right uu____23743
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
                              let uu____23801 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____23801 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23813::uu____23814 ->
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
                                         let uu____23859 =
                                           let uu____23870 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____23870)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____23859
                                     | uu____23895 -> tok_typing  in
                                   let uu____23904 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____23904 with
                                    | (vars',guards',env'',decls_formals,uu____23929)
                                        ->
                                        let uu____23942 =
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
                                        (match uu____23942 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____23973 ->
                                                   let uu____23980 =
                                                     let uu____23981 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____23981
                                                      in
                                                   [uu____23980]
                                                in
                                             let encode_elim uu____23991 =
                                               let uu____23992 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____23992 with
                                               | (head1,args) ->
                                                   let uu____24035 =
                                                     let uu____24036 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24036.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24035 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24046;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24047;_},uu____24048)
                                                        ->
                                                        let uu____24053 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24053
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24066
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24066
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
                                                                    uu____24109
                                                                    ->
                                                                    let uu____24110
                                                                    =
                                                                    let uu____24115
                                                                    =
                                                                    let uu____24116
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24116
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24115)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24110
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24132
                                                                    =
                                                                    let uu____24133
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24133
                                                                     in
                                                                    if
                                                                    uu____24132
                                                                    then
                                                                    let uu____24146
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24146]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24148
                                                                    =
                                                                    let uu____24161
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24211
                                                                     ->
                                                                    fun
                                                                    uu____24212
                                                                     ->
                                                                    match 
                                                                    (uu____24211,
                                                                    uu____24212)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24307
                                                                    =
                                                                    let uu____24314
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24314
                                                                     in
                                                                    (match uu____24307
                                                                    with
                                                                    | 
                                                                    (uu____24327,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24335
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24335
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24337
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24337
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
                                                                    uu____24161
                                                                     in
                                                                  (match uu____24148
                                                                   with
                                                                   | 
                                                                   (uu____24352,arg_vars,elim_eqns_or_guards,uu____24355)
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
                                                                    let uu____24383
                                                                    =
                                                                    let uu____24390
                                                                    =
                                                                    let uu____24391
                                                                    =
                                                                    let uu____24402
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24413
                                                                    =
                                                                    let uu____24414
                                                                    =
                                                                    let uu____24419
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24419)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24414
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24402,
                                                                    uu____24413)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24391
                                                                     in
                                                                    (uu____24390,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24383
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24442
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24442,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24444
                                                                    =
                                                                    let uu____24451
                                                                    =
                                                                    let uu____24452
                                                                    =
                                                                    let uu____24463
                                                                    =
                                                                    let uu____24468
                                                                    =
                                                                    let uu____24471
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____24471]
                                                                     in
                                                                    [uu____24468]
                                                                     in
                                                                    let uu____24476
                                                                    =
                                                                    let uu____24477
                                                                    =
                                                                    let uu____24482
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____24483
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____24482,
                                                                    uu____24483)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24477
                                                                     in
                                                                    (uu____24463,
                                                                    [x],
                                                                    uu____24476)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24452
                                                                     in
                                                                    let uu____24502
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24451,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24502)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24444
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24509
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
                                                                    (let uu____24537
                                                                    =
                                                                    let uu____24538
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24538
                                                                    dapp1  in
                                                                    [uu____24537])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24509
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____24545
                                                                    =
                                                                    let uu____24552
                                                                    =
                                                                    let uu____24553
                                                                    =
                                                                    let uu____24564
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24575
                                                                    =
                                                                    let uu____24576
                                                                    =
                                                                    let uu____24581
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____24581)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24576
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24564,
                                                                    uu____24575)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24553
                                                                     in
                                                                    (uu____24552,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24545)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____24601 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24601
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24614
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24614
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
                                                                    uu____24657
                                                                    ->
                                                                    let uu____24658
                                                                    =
                                                                    let uu____24663
                                                                    =
                                                                    let uu____24664
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24664
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24663)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24658
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24680
                                                                    =
                                                                    let uu____24681
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24681
                                                                     in
                                                                    if
                                                                    uu____24680
                                                                    then
                                                                    let uu____24694
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24694]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24696
                                                                    =
                                                                    let uu____24709
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24759
                                                                     ->
                                                                    fun
                                                                    uu____24760
                                                                     ->
                                                                    match 
                                                                    (uu____24759,
                                                                    uu____24760)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24855
                                                                    =
                                                                    let uu____24862
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24862
                                                                     in
                                                                    (match uu____24855
                                                                    with
                                                                    | 
                                                                    (uu____24875,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24883
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24883
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24885
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24885
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
                                                                    uu____24709
                                                                     in
                                                                  (match uu____24696
                                                                   with
                                                                   | 
                                                                   (uu____24900,arg_vars,elim_eqns_or_guards,uu____24903)
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
                                                                    let uu____24931
                                                                    =
                                                                    let uu____24938
                                                                    =
                                                                    let uu____24939
                                                                    =
                                                                    let uu____24950
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24961
                                                                    =
                                                                    let uu____24962
                                                                    =
                                                                    let uu____24967
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24967)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24962
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24950,
                                                                    uu____24961)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24939
                                                                     in
                                                                    (uu____24938,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24931
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24990
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24990,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24992
                                                                    =
                                                                    let uu____24999
                                                                    =
                                                                    let uu____25000
                                                                    =
                                                                    let uu____25011
                                                                    =
                                                                    let uu____25016
                                                                    =
                                                                    let uu____25019
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25019]
                                                                     in
                                                                    [uu____25016]
                                                                     in
                                                                    let uu____25024
                                                                    =
                                                                    let uu____25025
                                                                    =
                                                                    let uu____25030
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25031
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25030,
                                                                    uu____25031)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25025
                                                                     in
                                                                    (uu____25011,
                                                                    [x],
                                                                    uu____25024)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25000
                                                                     in
                                                                    let uu____25050
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24999,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25050)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24992
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25057
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
                                                                    (let uu____25085
                                                                    =
                                                                    let uu____25086
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25086
                                                                    dapp1  in
                                                                    [uu____25085])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25057
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25093
                                                                    =
                                                                    let uu____25100
                                                                    =
                                                                    let uu____25101
                                                                    =
                                                                    let uu____25112
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25123
                                                                    =
                                                                    let uu____25124
                                                                    =
                                                                    let uu____25129
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25129)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25124
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25112,
                                                                    uu____25123)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25101
                                                                     in
                                                                    (uu____25100,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25093)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____25148 ->
                                                        ((let uu____25150 =
                                                            let uu____25155 =
                                                              let uu____25156
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25157
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25156
                                                                uu____25157
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25155)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25150);
                                                         ([], [])))
                                                in
                                             let uu____25162 = encode_elim ()
                                                in
                                             (match uu____25162 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25182 =
                                                      let uu____25185 =
                                                        let uu____25188 =
                                                          let uu____25191 =
                                                            let uu____25194 =
                                                              let uu____25195
                                                                =
                                                                let uu____25206
                                                                  =
                                                                  let uu____25209
                                                                    =
                                                                    let uu____25210
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25210
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25209
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25206)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25195
                                                               in
                                                            [uu____25194]  in
                                                          let uu____25215 =
                                                            let uu____25218 =
                                                              let uu____25221
                                                                =
                                                                let uu____25224
                                                                  =
                                                                  let uu____25227
                                                                    =
                                                                    let uu____25230
                                                                    =
                                                                    let uu____25233
                                                                    =
                                                                    let uu____25234
                                                                    =
                                                                    let uu____25241
                                                                    =
                                                                    let uu____25242
                                                                    =
                                                                    let uu____25253
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25253)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25242
                                                                     in
                                                                    (uu____25241,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25234
                                                                     in
                                                                    let uu____25266
                                                                    =
                                                                    let uu____25269
                                                                    =
                                                                    let uu____25270
                                                                    =
                                                                    let uu____25277
                                                                    =
                                                                    let uu____25278
                                                                    =
                                                                    let uu____25289
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25300
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25289,
                                                                    uu____25300)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25278
                                                                     in
                                                                    (uu____25277,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25270
                                                                     in
                                                                    [uu____25269]
                                                                     in
                                                                    uu____25233
                                                                    ::
                                                                    uu____25266
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25230
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25227
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25224
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25221
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25218
                                                             in
                                                          FStar_List.append
                                                            uu____25191
                                                            uu____25215
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25188
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25185
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25182
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
           (fun uu____25346  ->
              fun se  ->
                match uu____25346 with
                | (g,env1) ->
                    let uu____25366 = encode_sigelt env1 se  in
                    (match uu____25366 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25423 =
        match uu____25423 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25455 ->
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
                 ((let uu____25461 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____25461
                   then
                     let uu____25462 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____25463 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____25464 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25462 uu____25463 uu____25464
                   else ());
                  (let uu____25466 = encode_term t1 env1  in
                   match uu____25466 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____25482 =
                         let uu____25489 =
                           let uu____25490 =
                             let uu____25491 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____25491
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____25490  in
                         new_term_constant_from_string env1 x uu____25489  in
                       (match uu____25482 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____25507 = FStar_Options.log_queries ()
                                 in
                              if uu____25507
                              then
                                let uu____25510 =
                                  let uu____25511 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____25512 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____25513 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25511 uu____25512 uu____25513
                                   in
                                FStar_Pervasives_Native.Some uu____25510
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25529,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____25543 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____25543 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25566,se,uu____25568) ->
                 let uu____25573 = encode_sigelt env1 se  in
                 (match uu____25573 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25590,se) ->
                 let uu____25596 = encode_sigelt env1 se  in
                 (match uu____25596 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____25613 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____25613 with | (uu____25636,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____25648 'Auu____25649 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____25649,'Auu____25648)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25717  ->
              match uu____25717 with
              | (l,uu____25729,uu____25730) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____25776  ->
              match uu____25776 with
              | (l,uu____25790,uu____25791) ->
                  let uu____25800 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____25801 =
                    let uu____25804 =
                      let uu____25805 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____25805  in
                    [uu____25804]  in
                  uu____25800 :: uu____25801))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____25830 =
      let uu____25833 =
        let uu____25834 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____25837 =
          let uu____25838 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____25838 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____25834;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____25837
        }  in
      [uu____25833]  in
    FStar_ST.op_Colon_Equals last_env uu____25830
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____25868 = FStar_ST.op_Bang last_env  in
      match uu____25868 with
      | [] -> failwith "No env; call init first!"
      | e::uu____25895 ->
          let uu___131_25898 = e  in
          let uu____25899 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___131_25898.bindings);
            depth = (uu___131_25898.depth);
            tcenv;
            warn = (uu___131_25898.warn);
            cache = (uu___131_25898.cache);
            nolabels = (uu___131_25898.nolabels);
            use_zfuel_name = (uu___131_25898.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_25898.encode_non_total_function_typ);
            current_module_name = uu____25899
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____25903 = FStar_ST.op_Bang last_env  in
    match uu____25903 with
    | [] -> failwith "Empty env stack"
    | uu____25929::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____25958  ->
    let uu____25959 = FStar_ST.op_Bang last_env  in
    match uu____25959 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___132_25993 = hd1  in
          {
            bindings = (uu___132_25993.bindings);
            depth = (uu___132_25993.depth);
            tcenv = (uu___132_25993.tcenv);
            warn = (uu___132_25993.warn);
            cache = refs;
            nolabels = (uu___132_25993.nolabels);
            use_zfuel_name = (uu___132_25993.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_25993.encode_non_total_function_typ);
            current_module_name = (uu___132_25993.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____26019  ->
    let uu____26020 = FStar_ST.op_Bang last_env  in
    match uu____26020 with
    | [] -> failwith "Popping an empty stack"
    | uu____26046::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____26110::uu____26111,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___133_26119 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___133_26119.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___133_26119.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___133_26119.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26120 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26135 =
        let uu____26138 =
          let uu____26139 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26139  in
        let uu____26140 = open_fact_db_tags env  in uu____26138 ::
          uu____26140
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26135
  
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
      let uu____26162 = encode_sigelt env se  in
      match uu____26162 with
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
        let uu____26198 = FStar_Options.log_queries ()  in
        if uu____26198
        then
          let uu____26201 =
            let uu____26202 =
              let uu____26203 =
                let uu____26204 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26204 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26203  in
            FStar_SMTEncoding_Term.Caption uu____26202  in
          uu____26201 :: decls
        else decls  in
      (let uu____26215 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26215
       then
         let uu____26216 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26216
       else ());
      (let env =
         let uu____26219 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26219 tcenv  in
       let uu____26220 = encode_top_level_facts env se  in
       match uu____26220 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26234 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26234)))
  
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
      (let uu____26246 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26246
       then
         let uu____26247 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26247
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26282  ->
                 fun se  ->
                   match uu____26282 with
                   | (g,env2) ->
                       let uu____26302 = encode_top_level_facts env2 se  in
                       (match uu____26302 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26325 =
         encode_signature
           (let uu___134_26334 = env  in
            {
              bindings = (uu___134_26334.bindings);
              depth = (uu___134_26334.depth);
              tcenv = (uu___134_26334.tcenv);
              warn = false;
              cache = (uu___134_26334.cache);
              nolabels = (uu___134_26334.nolabels);
              use_zfuel_name = (uu___134_26334.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_26334.encode_non_total_function_typ);
              current_module_name = (uu___134_26334.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26325 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26351 = FStar_Options.log_queries ()  in
             if uu____26351
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___135_26359 = env1  in
               {
                 bindings = (uu___135_26359.bindings);
                 depth = (uu___135_26359.depth);
                 tcenv = (uu___135_26359.tcenv);
                 warn = true;
                 cache = (uu___135_26359.cache);
                 nolabels = (uu___135_26359.nolabels);
                 use_zfuel_name = (uu___135_26359.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___135_26359.encode_non_total_function_typ);
                 current_module_name = (uu___135_26359.current_module_name)
               });
            (let uu____26361 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____26361
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
        (let uu____26413 =
           let uu____26414 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____26414.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26413);
        (let env =
           let uu____26416 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____26416 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____26428 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26463 = aux rest  in
                 (match uu____26463 with
                  | (out,rest1) ->
                      let t =
                        let uu____26493 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____26493 with
                        | FStar_Pervasives_Native.Some uu____26498 ->
                            let uu____26499 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____26499
                              x.FStar_Syntax_Syntax.sort
                        | uu____26500 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____26504 =
                        let uu____26507 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___136_26510 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_26510.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_26510.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____26507 :: out  in
                      (uu____26504, rest1))
             | uu____26515 -> ([], bindings1)  in
           let uu____26522 = aux bindings  in
           match uu____26522 with
           | (closing,bindings1) ->
               let uu____26547 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____26547, bindings1)
            in
         match uu____26428 with
         | (q1,bindings1) ->
             let uu____26570 =
               let uu____26575 =
                 FStar_List.filter
                   (fun uu___101_26580  ->
                      match uu___101_26580 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26581 ->
                          false
                      | uu____26588 -> true) bindings1
                  in
               encode_env_bindings env uu____26575  in
             (match uu____26570 with
              | (env_decls,env1) ->
                  ((let uu____26606 =
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
                    if uu____26606
                    then
                      let uu____26607 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26607
                    else ());
                   (let uu____26609 = encode_formula q1 env1  in
                    match uu____26609 with
                    | (phi,qdecls) ->
                        let uu____26630 =
                          let uu____26635 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26635 phi
                           in
                        (match uu____26630 with
                         | (labels,phi1) ->
                             let uu____26652 = encode_labels labels  in
                             (match uu____26652 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____26689 =
                                      let uu____26696 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____26697 =
                                        varops.mk_unique "@query"  in
                                      (uu____26696,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26697)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26689
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
  