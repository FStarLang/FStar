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
          mk_fvb x fvb.smt_id (fvb.smt_arity - (Prims.parse_int "1"))
            fvb.smt_token (FStar_Pervasives_Native.Some t3)
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
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string)
  =
  fun env  ->
    fun a  -> let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in fvb.smt_id
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let uu____2548 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____2548 with
      | { fvar_lid = uu____2555; smt_arity = uu____2556; smt_id = name;
          smt_token = sym; smt_fuel_partial_app = zf_opt;_} ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2572;
                 FStar_SMTEncoding_Term.rng = uu____2573;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2588 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2612 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___85_2625  ->
           match uu___85_2625 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____2629 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____2633 .
    'Auu____2633 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____2651  ->
      match uu____2651 with
      | (pats,vars,body) ->
          let fallback uu____2676 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____2681 = FStar_Options.unthrottle_inductives ()  in
          if uu____2681
          then fallback ()
          else
            (let uu____2683 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____2683 with
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
                           | uu____2714 -> p))
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
                             let uu____2735 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____2735
                         | uu____2738 ->
                             let uu____2739 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____2739 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____2744 -> body  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____2785 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2798 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2805 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2806 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2823 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2840 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2842 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2842 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2860;
             FStar_Syntax_Syntax.vars = uu____2861;_},uu____2862)
          ->
          let uu____2883 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2883 FStar_Option.isNone
      | uu____2900 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____2907 =
        let uu____2908 = FStar_Syntax_Util.un_uinst t  in
        uu____2908.FStar_Syntax_Syntax.n  in
      match uu____2907 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2911,uu____2912,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___86_2933  ->
                  match uu___86_2933 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2934 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2936 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2936 FStar_Option.isSome
      | uu____2953 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____2960 = head_normal env t  in
      if uu____2960
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
    let uu____2971 =
      let uu____2972 = FStar_Syntax_Syntax.null_binder t  in [uu____2972]  in
    let uu____2973 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____2971 uu____2973 FStar_Pervasives_Native.None
  
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
                    let uu____3011 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3011
                | s ->
                    let uu____3016 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3016) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___87_3031  ->
    match uu___87_3031 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3032 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____3068;
                       FStar_SMTEncoding_Term.rng = uu____3069;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3092) ->
              let uu____3101 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3112 -> false) args (FStar_List.rev xs))
                 in
              if uu____3101
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3116,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3120 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3124 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3124))
                 in
              if uu____3120
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3128 -> FStar_Pervasives_Native.None  in
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
    | uu____3350 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3354 -> false
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3373 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3386 ->
            let uu____3393 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3393
        | uu____3394 ->
            if norm1
            then let uu____3395 = whnf env t1  in aux false uu____3395
            else
              (let uu____3397 =
                 let uu____3398 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3399 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3398 uu____3399
                  in
               failwith uu____3397)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3431) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3436 ->
        let uu____3437 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3437)
  
let is_arithmetic_primitive :
  'Auu____3451 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3451 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3471::uu____3472::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3476::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3479 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3500 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3515 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____3519 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3519)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____3558)::uu____3559::uu____3560::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3611)::uu____3612::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____3649 -> false
  
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
          let uu____3868 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____3868, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____3871 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____3871, [])
      | FStar_Const.Const_char c1 ->
          let uu____3875 =
            let uu____3876 =
              let uu____3883 =
                let uu____3886 =
                  let uu____3887 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____3887  in
                [uu____3886]  in
              ("FStar.Char.__char_of_int", uu____3883)  in
            FStar_SMTEncoding_Util.mkApp uu____3876  in
          (uu____3875, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____3903 =
            let uu____3904 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____3904  in
          (uu____3903, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____3925) ->
          let uu____3926 = varops.string_const s  in (uu____3926, [])
      | FStar_Const.Const_range uu____3929 ->
          let uu____3930 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____3930, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____3936 =
            let uu____3937 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____3937  in
          failwith uu____3936

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
        (let uu____3966 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____3966
         then
           let uu____3967 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____3967
         else ());
        (let uu____3969 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4053  ->
                   fun b  ->
                     match uu____4053 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4132 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4148 = gen_term_var env1 x  in
                           match uu____4148 with
                           | (xxsym,xx,env') ->
                               let uu____4172 =
                                 let uu____4177 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4177 env1 xx
                                  in
                               (match uu____4172 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4132 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____3969 with
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
          let uu____4336 = encode_term t env  in
          match uu____4336 with
          | (t1,decls) ->
              let uu____4347 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____4347, decls)

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
          let uu____4358 = encode_term t env  in
          match uu____4358 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4373 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____4373, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4375 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____4375, decls))

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
        let uu____4381 = encode_args args_e env  in
        match uu____4381 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4400 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____4409 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____4409  in
            let binary arg_tms1 =
              let uu____4422 =
                let uu____4423 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____4423  in
              let uu____4424 =
                let uu____4425 =
                  let uu____4426 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____4426  in
                FStar_SMTEncoding_Term.unboxInt uu____4425  in
              (uu____4422, uu____4424)  in
            let mk_default uu____4432 =
              let uu____4433 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4433 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l a op mk_args ts =
              let uu____4479 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____4479
              then
                let uu____4480 =
                  let uu____4481 = mk_args ts  in op uu____4481  in
                FStar_All.pipe_right uu____4480 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____4510 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____4510
              then
                let uu____4511 = binary ts  in
                match uu____4511 with
                | (t1,t2) ->
                    let uu____4518 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____4518
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4522 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____4522
                 then
                   let uu____4523 = op (binary ts)  in
                   FStar_All.pipe_right uu____4523
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
            let uu____4646 =
              let uu____4655 =
                FStar_List.tryFind
                  (fun uu____4677  ->
                     match uu____4677 with
                     | (l,uu____4687) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____4655 FStar_Util.must  in
            (match uu____4646 with
             | (uu____4726,op) ->
                 let uu____4736 = op arg_tms  in (uu____4736, decls))

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
        let uu____4744 = FStar_List.hd args_e  in
        match uu____4744 with
        | (tm_sz,uu____4752) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____4762 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____4762 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
                  ((let uu____4770 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____4770);
                   t_decls)
               in
            let uu____4771 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____4791::(sz_arg,uu____4793)::uu____4794::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____4843 =
                    let uu____4846 = FStar_List.tail args_e  in
                    FStar_List.tail uu____4846  in
                  let uu____4849 =
                    let uu____4852 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____4852  in
                  (uu____4843, uu____4849)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____4858::(sz_arg,uu____4860)::uu____4861::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____4910 =
                    let uu____4911 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____4911
                     in
                  failwith uu____4910
              | uu____4920 ->
                  let uu____4927 = FStar_List.tail args_e  in
                  (uu____4927, FStar_Pervasives_Native.None)
               in
            (match uu____4771 with
             | (arg_tms,ext_sz) ->
                 let uu____4950 = encode_args arg_tms env  in
                 (match uu____4950 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____4971 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____4980 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____4980  in
                      let unary_arith arg_tms2 =
                        let uu____4989 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____4989  in
                      let binary arg_tms2 =
                        let uu____5002 =
                          let uu____5003 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5003
                           in
                        let uu____5004 =
                          let uu____5005 =
                            let uu____5006 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5006  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5005
                           in
                        (uu____5002, uu____5004)  in
                      let binary_arith arg_tms2 =
                        let uu____5021 =
                          let uu____5022 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5022
                           in
                        let uu____5023 =
                          let uu____5024 =
                            let uu____5025 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5025  in
                          FStar_SMTEncoding_Term.unboxInt uu____5024  in
                        (uu____5021, uu____5023)  in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5067 =
                          let uu____5068 = mk_args ts  in op uu____5068  in
                        FStar_All.pipe_right uu____5067 resBox  in
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
                        let uu____5132 =
                          let uu____5135 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5135  in
                        let uu____5137 =
                          let uu____5140 =
                            let uu____5141 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5141  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5140  in
                        mk_bv () (fun a443  -> (Obj.magic uu____5132) a443)
                          (fun a444  -> (Obj.magic unary) a444) uu____5137
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
                      let uu____5340 =
                        let uu____5349 =
                          FStar_List.tryFind
                            (fun uu____5371  ->
                               match uu____5371 with
                               | (l,uu____5381) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____5349 FStar_Util.must  in
                      (match uu____5340 with
                       | (uu____5422,op) ->
                           let uu____5432 = op arg_tms1  in
                           (uu____5432, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____5443 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____5443
       then
         let uu____5444 = FStar_Syntax_Print.tag_of_term t  in
         let uu____5445 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____5446 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5444 uu____5445
           uu____5446
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5452 ->
           let uu____5477 =
             let uu____5478 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5479 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5480 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5481 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5478
               uu____5479 uu____5480 uu____5481
              in
           failwith uu____5477
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5486 =
             let uu____5487 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5488 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5489 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5490 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5487
               uu____5488 uu____5489 uu____5490
              in
           failwith uu____5486
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5496 =
             let uu____5497 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5497
              in
           failwith uu____5496
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____5504),uu____5505) ->
           let uu____5554 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____5562 -> false  in
           if uu____5554
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____5578;
              FStar_Syntax_Syntax.vars = uu____5579;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____5596 = varops.fresh "t"  in
             (uu____5596, FStar_SMTEncoding_Term.Term_sort)  in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym  in
           let decl =
             let uu____5599 =
               let uu____5610 =
                 let uu____5613 = FStar_Util.format1 "alien term (%s)" desc
                    in
                 FStar_Pervasives_Native.Some uu____5613  in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____5610)
                in
             FStar_SMTEncoding_Term.DeclFun uu____5599  in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5621) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5631 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____5631, [])
       | FStar_Syntax_Syntax.Tm_type uu____5634 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5638) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____5663 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5663 with
            | (binders1,res) ->
                let uu____5674 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5674
                then
                  let uu____5679 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5679 with
                   | (vars,guards,env',decls,uu____5704) ->
                       let fsym =
                         let uu____5722 = varops.fresh "f"  in
                         (uu____5722, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5725 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___111_5734 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___111_5734.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___111_5734.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___111_5734.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___111_5734.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___111_5734.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___111_5734.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___111_5734.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___111_5734.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___111_5734.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___111_5734.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___111_5734.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___111_5734.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___111_5734.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___111_5734.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___111_5734.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___111_5734.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___111_5734.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___111_5734.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___111_5734.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___111_5734.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___111_5734.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___111_5734.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___111_5734.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___111_5734.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___111_5734.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___111_5734.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___111_5734.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___111_5734.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___111_5734.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___111_5734.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___111_5734.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___111_5734.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___111_5734.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___111_5734.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____5725 with
                        | (pre_opt,res_t) ->
                            let uu____5745 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5745 with
                             | (res_pred,decls') ->
                                 let uu____5756 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5769 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____5769, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5773 =
                                         encode_formula pre env'  in
                                       (match uu____5773 with
                                        | (guard,decls0) ->
                                            let uu____5786 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____5786, decls0))
                                    in
                                 (match uu____5756 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____5798 =
                                          let uu____5809 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____5809)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5798
                                         in
                                      let cvars =
                                        let uu____5827 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____5827
                                          (FStar_List.filter
                                             (fun uu____5841  ->
                                                match uu____5841 with
                                                | (x,uu____5847) ->
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
                                      let uu____5866 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____5866 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5874 =
                                             let uu____5875 =
                                               let uu____5882 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5882)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5875
                                              in
                                           (uu____5874,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____5902 =
                                               let uu____5903 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____5903
                                                in
                                             varops.mk_unique uu____5902  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____5914 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____5914
                                             then
                                               let uu____5917 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____5917
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
                                             let uu____5925 =
                                               let uu____5932 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____5932)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5925
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
                                             let uu____5944 =
                                               let uu____5951 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____5951,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5944
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
                                             let uu____5972 =
                                               let uu____5979 =
                                                 let uu____5980 =
                                                   let uu____5991 =
                                                     let uu____5992 =
                                                       let uu____5997 =
                                                         let uu____5998 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____5998
                                                          in
                                                       (f_has_t, uu____5997)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____5992
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____5991)
                                                    in
                                                 mkForall_fuel uu____5980  in
                                               (uu____5979,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5972
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6021 =
                                               let uu____6028 =
                                                 let uu____6029 =
                                                   let uu____6040 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6040)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6029
                                                  in
                                               (uu____6028,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6021
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
                                           ((let uu____6065 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6065);
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
                     let uu____6080 =
                       let uu____6087 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6087,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6080  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6099 =
                       let uu____6106 =
                         let uu____6107 =
                           let uu____6118 =
                             let uu____6119 =
                               let uu____6124 =
                                 let uu____6125 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6125
                                  in
                               (f_has_t, uu____6124)  in
                             FStar_SMTEncoding_Util.mkImp uu____6119  in
                           ([[f_has_t]], [fsym], uu____6118)  in
                         mkForall_fuel uu____6107  in
                       (uu____6106, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6099  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6152 ->
           let uu____6159 =
             let uu____6164 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6164 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6171;
                 FStar_Syntax_Syntax.vars = uu____6172;_} ->
                 let uu____6179 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6179 with
                  | (b,f1) ->
                      let uu____6204 =
                        let uu____6205 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6205  in
                      (uu____6204, f1))
             | uu____6214 -> failwith "impossible"  in
           (match uu____6159 with
            | (x,f) ->
                let uu____6225 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6225 with
                 | (base_t,decls) ->
                     let uu____6236 = gen_term_var env x  in
                     (match uu____6236 with
                      | (x1,xtm,env') ->
                          let uu____6250 = encode_formula f env'  in
                          (match uu____6250 with
                           | (refinement,decls') ->
                               let uu____6261 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6261 with
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
                                      let uu____6277 =
                                        let uu____6280 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6287 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6280
                                          uu____6287
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6277
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6320  ->
                                              match uu____6320 with
                                              | (y,uu____6326) ->
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
                                    let uu____6359 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6359 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6367 =
                                           let uu____6368 =
                                             let uu____6375 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6375)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6368
                                            in
                                         (uu____6367,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6396 =
                                             let uu____6397 =
                                               let uu____6398 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6398
                                                in
                                             Prims.strcat module_name
                                               uu____6397
                                              in
                                           varops.mk_unique uu____6396  in
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
                                           let uu____6412 =
                                             let uu____6419 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6419)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6412
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
                                           let uu____6434 =
                                             let uu____6441 =
                                               let uu____6442 =
                                                 let uu____6453 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6453)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6442
                                                in
                                             (uu____6441,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6434
                                            in
                                         let t_kinding =
                                           let uu____6471 =
                                             let uu____6478 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6478,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6471
                                            in
                                         let t_interp =
                                           let uu____6496 =
                                             let uu____6503 =
                                               let uu____6504 =
                                                 let uu____6515 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6515)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6504
                                                in
                                             let uu____6538 =
                                               let uu____6541 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6541
                                                in
                                             (uu____6503, uu____6538,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6496
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____6548 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6548);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6578 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6578  in
           let uu____6579 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____6579 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6591 =
                    let uu____6598 =
                      let uu____6599 =
                        let uu____6600 =
                          let uu____6601 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6601
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____6600  in
                      varops.mk_unique uu____6599  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6598)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6591  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6606 ->
           let uu____6621 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6621 with
            | (head1,args_e) ->
                let uu____6662 =
                  let uu____6675 =
                    let uu____6676 = FStar_Syntax_Subst.compress head1  in
                    uu____6676.FStar_Syntax_Syntax.n  in
                  (uu____6675, args_e)  in
                (match uu____6662 with
                 | uu____6691 when head_redex env head1 ->
                     let uu____6704 = whnf env t  in
                     encode_term uu____6704 env
                 | uu____6705 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6724 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6738;
                       FStar_Syntax_Syntax.vars = uu____6739;_},uu____6740),uu____6741::
                    (v1,uu____6743)::(v2,uu____6745)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6796 = encode_term v1 env  in
                     (match uu____6796 with
                      | (v11,decls1) ->
                          let uu____6807 = encode_term v2 env  in
                          (match uu____6807 with
                           | (v21,decls2) ->
                               let uu____6818 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6818,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6822::(v1,uu____6824)::(v2,uu____6826)::[]) when
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
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6899)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6925)::(rng,uu____6927)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6962) ->
                     let e0 =
                       let uu____6980 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____6980
                        in
                     ((let uu____6988 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6988
                       then
                         let uu____6989 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6989
                       else ());
                      (let e =
                         let uu____6994 =
                           let uu____6995 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6996 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6995
                             uu____6996
                            in
                         uu____6994 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7005),(arg,uu____7007)::[]) -> encode_term arg env
                 | uu____7032 ->
                     let uu____7045 = encode_args args_e env  in
                     (match uu____7045 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7100 = encode_term head1 env  in
                            match uu____7100 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7164 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7164 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7242  ->
                                                 fun uu____7243  ->
                                                   match (uu____7242,
                                                           uu____7243)
                                                   with
                                                   | ((bv,uu____7265),
                                                      (a,uu____7267)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7285 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7285
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7290 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7290 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7305 =
                                                   let uu____7312 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7321 =
                                                     let uu____7322 =
                                                       let uu____7323 =
                                                         let uu____7324 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7324
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7323
                                                        in
                                                     varops.mk_unique
                                                       uu____7322
                                                      in
                                                   (uu____7312,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7321)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7305
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7341 = lookup_free_var_sym env fv  in
                            match uu____7341 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args))
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
                                   FStar_Syntax_Syntax.pos = uu____7372;
                                   FStar_Syntax_Syntax.vars = uu____7373;_},uu____7374)
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
                                   FStar_Syntax_Syntax.pos = uu____7385;
                                   FStar_Syntax_Syntax.vars = uu____7386;_},uu____7387)
                                ->
                                let uu____7392 =
                                  let uu____7393 =
                                    let uu____7398 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7398
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7393
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7392
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7428 =
                                  let uu____7429 =
                                    let uu____7434 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7434
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7429
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7428
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7463,(FStar_Util.Inl t1,uu____7465),uu____7466)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7515,(FStar_Util.Inr c,uu____7517),uu____7518)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7567 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7594 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7594
                                  in
                               let uu____7595 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7595 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7611;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7612;_},uu____7613)
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
                                     | uu____7627 ->
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
           let uu____7676 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7676 with
            | (bs1,body1,opening) ->
                let fallback uu____7699 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7706 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7706, [decl])  in
                let is_impure rc =
                  let uu____7713 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7713 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7723 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____7723
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____7743 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7743
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____7747 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7747)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7754 =
                         let uu____7759 =
                           let uu____7760 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7760
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7759)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7754);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7762 =
                       (is_impure rc) &&
                         (let uu____7764 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____7764)
                        in
                     if uu____7762
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____7771 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7771 with
                        | (vars,guards,envbody,decls,uu____7796) ->
                            let body2 =
                              let uu____7810 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____7810
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____7812 = encode_term body2 envbody  in
                            (match uu____7812 with
                             | (body3,decls') ->
                                 let uu____7823 =
                                   let uu____7832 = codomain_eff rc  in
                                   match uu____7832 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7851 = encode_term tfun env
                                          in
                                       (match uu____7851 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7823 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7883 =
                                          let uu____7894 =
                                            let uu____7895 =
                                              let uu____7900 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7900, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7895
                                             in
                                          ([], vars, uu____7894)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____7883
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
                                            let uu____7912 =
                                              let uu____7915 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____7915
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____7912
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____7934 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____7934 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____7942 =
                                             let uu____7943 =
                                               let uu____7950 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____7950)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7943
                                              in
                                           (uu____7942,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____7961 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7961 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____7972 =
                                                    let uu____7973 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____7973 = cache_size
                                                     in
                                                  if uu____7972
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
                                                    let uu____7989 =
                                                      let uu____7990 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____7990
                                                       in
                                                    varops.mk_unique
                                                      uu____7989
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
                                                  let uu____7997 =
                                                    let uu____8004 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8004)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7997
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
                                                      let uu____8022 =
                                                        let uu____8023 =
                                                          let uu____8030 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8030,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8023
                                                         in
                                                      [uu____8022]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8043 =
                                                    let uu____8050 =
                                                      let uu____8051 =
                                                        let uu____8062 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8062)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8051
                                                       in
                                                    (uu____8050,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8043
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
                                                ((let uu____8079 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8079);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8082,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8083;
                          FStar_Syntax_Syntax.lbunivs = uu____8084;
                          FStar_Syntax_Syntax.lbtyp = uu____8085;
                          FStar_Syntax_Syntax.lbeff = uu____8086;
                          FStar_Syntax_Syntax.lbdef = uu____8087;
                          FStar_Syntax_Syntax.lbattrs = uu____8088;_}::uu____8089),uu____8090)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8120;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8122;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8124;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8148 ->
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
              let uu____8218 =
                let uu____8223 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8223 env  in
              match uu____8218 with
              | (ee1,decls1) ->
                  let uu____8244 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8244 with
                   | (xs,e21) ->
                       let uu____8269 = FStar_List.hd xs  in
                       (match uu____8269 with
                        | (x1,uu____8283) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8285 = encode_body e21 env'  in
                            (match uu____8285 with
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
            let uu____8317 =
              let uu____8324 =
                let uu____8325 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8325  in
              gen_term_var env uu____8324  in
            match uu____8317 with
            | (scrsym,scr',env1) ->
                let uu____8333 = encode_term e env1  in
                (match uu____8333 with
                 | (scr,decls) ->
                     let uu____8344 =
                       let encode_branch b uu____8369 =
                         match uu____8369 with
                         | (else_case,decls1) ->
                             let uu____8388 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8388 with
                              | (p,w,br) ->
                                  let uu____8414 = encode_pat env1 p  in
                                  (match uu____8414 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8451  ->
                                                   match uu____8451 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8458 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8480 =
                                               encode_term w1 env2  in
                                             (match uu____8480 with
                                              | (w2,decls2) ->
                                                  let uu____8493 =
                                                    let uu____8494 =
                                                      let uu____8499 =
                                                        let uu____8500 =
                                                          let uu____8505 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8505)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8500
                                                         in
                                                      (guard, uu____8499)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8494
                                                     in
                                                  (uu____8493, decls2))
                                          in
                                       (match uu____8458 with
                                        | (guard1,decls2) ->
                                            let uu____8518 =
                                              encode_br br env2  in
                                            (match uu____8518 with
                                             | (br1,decls3) ->
                                                 let uu____8531 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8531,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8344 with
                      | (match_tm,decls1) ->
                          let uu____8550 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8550, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____8590 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____8590
       then
         let uu____8591 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8591
       else ());
      (let uu____8593 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8593 with
       | (vars,pat_term) ->
           let uu____8610 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8663  ->
                     fun v1  ->
                       match uu____8663 with
                       | (env1,vars1) ->
                           let uu____8715 = gen_term_var env1 v1  in
                           (match uu____8715 with
                            | (xx,uu____8737,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8610 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8816 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8817 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8818 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8826 = encode_const c env1  in
                      (match uu____8826 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8840::uu____8841 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8844 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8867 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____8867 with
                        | (uu____8874,uu____8875::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8878 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8911  ->
                                  match uu____8911 with
                                  | (arg,uu____8919) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8925 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8925))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8952) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8983 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9006 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9050  ->
                                  match uu____9050 with
                                  | (arg,uu____9064) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9070 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9070))
                         in
                      FStar_All.pipe_right uu____9006 FStar_List.flatten
                   in
                let pat_term1 uu____9098 = encode_term pat_term env1  in
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
      let uu____9108 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9146  ->
                fun uu____9147  ->
                  match (uu____9146, uu____9147) with
                  | ((tms,decls),(t,uu____9183)) ->
                      let uu____9204 = encode_term t env  in
                      (match uu____9204 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9108 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9261 = FStar_Syntax_Util.list_elements e  in
        match uu____9261 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9282 =
          let uu____9297 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9297 FStar_Syntax_Util.head_and_args  in
        match uu____9282 with
        | (head1,args) ->
            let uu____9336 =
              let uu____9349 =
                let uu____9350 = FStar_Syntax_Util.un_uinst head1  in
                uu____9350.FStar_Syntax_Syntax.n  in
              (uu____9349, args)  in
            (match uu____9336 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9364,uu____9365)::(e,uu____9367)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9402 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9438 =
            let uu____9453 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9453 FStar_Syntax_Util.head_and_args
             in
          match uu____9438 with
          | (head1,args) ->
              let uu____9494 =
                let uu____9507 =
                  let uu____9508 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9508.FStar_Syntax_Syntax.n  in
                (uu____9507, args)  in
              (match uu____9494 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9525)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9552 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9574 = smt_pat_or1 t1  in
            (match uu____9574 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9590 = list_elements1 e  in
                 FStar_All.pipe_right uu____9590
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9608 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9608
                           (FStar_List.map one_pat)))
             | uu____9619 ->
                 let uu____9624 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9624])
        | uu____9645 ->
            let uu____9648 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9648]
         in
      let uu____9669 =
        let uu____9688 =
          let uu____9689 = FStar_Syntax_Subst.compress t  in
          uu____9689.FStar_Syntax_Syntax.n  in
        match uu____9688 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9728 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9728 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9771;
                        FStar_Syntax_Syntax.effect_name = uu____9772;
                        FStar_Syntax_Syntax.result_typ = uu____9773;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9775)::(post,uu____9777)::(pats,uu____9779)::[];
                        FStar_Syntax_Syntax.flags = uu____9780;_}
                      ->
                      let uu____9821 = lemma_pats pats  in
                      (binders1, pre, post, uu____9821)
                  | uu____9838 -> failwith "impos"))
        | uu____9857 -> failwith "Impos"  in
      match uu____9669 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___112_9905 = env  in
            {
              bindings = (uu___112_9905.bindings);
              depth = (uu___112_9905.depth);
              tcenv = (uu___112_9905.tcenv);
              warn = (uu___112_9905.warn);
              cache = (uu___112_9905.cache);
              nolabels = (uu___112_9905.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___112_9905.encode_non_total_function_typ);
              current_module_name = (uu___112_9905.current_module_name)
            }  in
          let uu____9906 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9906 with
           | (vars,guards,env2,decls,uu____9931) ->
               let uu____9944 =
                 let uu____9959 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10013 =
                             let uu____10024 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10024
                               FStar_List.unzip
                              in
                           match uu____10013 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____9959 FStar_List.unzip  in
               (match uu____9944 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___113_10176 = env2  in
                      {
                        bindings = (uu___113_10176.bindings);
                        depth = (uu___113_10176.depth);
                        tcenv = (uu___113_10176.tcenv);
                        warn = (uu___113_10176.warn);
                        cache = (uu___113_10176.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___113_10176.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___113_10176.encode_non_total_function_typ);
                        current_module_name =
                          (uu___113_10176.current_module_name)
                      }  in
                    let uu____10177 =
                      let uu____10182 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10182 env3  in
                    (match uu____10177 with
                     | (pre1,decls'') ->
                         let uu____10189 =
                           let uu____10194 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10194 env3  in
                         (match uu____10189 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10204 =
                                let uu____10205 =
                                  let uu____10216 =
                                    let uu____10217 =
                                      let uu____10222 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10222, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10217
                                     in
                                  (pats, vars, uu____10216)  in
                                FStar_SMTEncoding_Util.mkForall uu____10205
                                 in
                              (uu____10204, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____10235 = FStar_Syntax_Util.head_and_args t  in
      match uu____10235 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10294::(x,uu____10296)::(t1,uu____10298)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10345 = encode_term x env  in
               (match uu____10345 with
                | (x1,decls) ->
                    let uu____10358 = encode_term t1 env  in
                    (match uu____10358 with
                     | (t2,decls') ->
                         let uu____10371 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10371, (FStar_List.append decls decls'))))
           | uu____10374 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10397 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10397
        then
          let uu____10398 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10399 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10398 uu____10399
        else ()  in
      let enc f r l =
        let uu____10432 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10460 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10460 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10432 with
        | (decls,args) ->
            let uu____10489 =
              let uu___114_10490 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10490.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10490.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10489, decls)
         in
      let const_op f r uu____10521 =
        let uu____10534 = f r  in (uu____10534, [])  in
      let un_op f l =
        let uu____10553 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10553  in
      let bin_op f uu___88_10569 =
        match uu___88_10569 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10580 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10614 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10637  ->
                 match uu____10637 with
                 | (t,uu____10651) ->
                     let uu____10652 = encode_formula t env  in
                     (match uu____10652 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10614 with
        | (decls,phis) ->
            let uu____10681 =
              let uu___115_10682 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___115_10682.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___115_10682.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10681, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10743  ->
               match uu____10743 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10762) -> false
                    | uu____10763 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10778 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10778
        else
          (let uu____10792 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10792 r rf)
         in
      let mk_imp1 r uu___89_10817 =
        match uu___89_10817 with
        | (lhs,uu____10823)::(rhs,uu____10825)::[] ->
            let uu____10852 = encode_formula rhs env  in
            (match uu____10852 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10867) ->
                      (l1, decls1)
                  | uu____10872 ->
                      let uu____10873 = encode_formula lhs env  in
                      (match uu____10873 with
                       | (l2,decls2) ->
                           let uu____10884 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10884, (FStar_List.append decls1 decls2)))))
        | uu____10887 -> failwith "impossible"  in
      let mk_ite r uu___90_10908 =
        match uu___90_10908 with
        | (guard,uu____10914)::(_then,uu____10916)::(_else,uu____10918)::[]
            ->
            let uu____10955 = encode_formula guard env  in
            (match uu____10955 with
             | (g,decls1) ->
                 let uu____10966 = encode_formula _then env  in
                 (match uu____10966 with
                  | (t,decls2) ->
                      let uu____10977 = encode_formula _else env  in
                      (match uu____10977 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10991 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11016 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11016  in
      let connectives =
        let uu____11034 =
          let uu____11047 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11047)  in
        let uu____11064 =
          let uu____11079 =
            let uu____11092 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11092)  in
          let uu____11109 =
            let uu____11124 =
              let uu____11139 =
                let uu____11152 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11152)  in
              let uu____11169 =
                let uu____11184 =
                  let uu____11199 =
                    let uu____11212 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11212)  in
                  [uu____11199;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11184  in
              uu____11139 :: uu____11169  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11124  in
          uu____11079 :: uu____11109  in
        uu____11034 :: uu____11064  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11533 = encode_formula phi' env  in
            (match uu____11533 with
             | (phi2,decls) ->
                 let uu____11544 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11544, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11545 ->
            let uu____11552 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11552 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11591 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11591 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11603;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11605;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11607;_}::[]),e2)
            ->
            let uu____11631 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11631 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11678::(x,uu____11680)::(t,uu____11682)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11729 = encode_term x env  in
                 (match uu____11729 with
                  | (x1,decls) ->
                      let uu____11740 = encode_term t env  in
                      (match uu____11740 with
                       | (t1,decls') ->
                           let uu____11751 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11751, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11756)::(msg,uu____11758)::(phi2,uu____11760)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11805 =
                   let uu____11810 =
                     let uu____11811 = FStar_Syntax_Subst.compress r  in
                     uu____11811.FStar_Syntax_Syntax.n  in
                   let uu____11814 =
                     let uu____11815 = FStar_Syntax_Subst.compress msg  in
                     uu____11815.FStar_Syntax_Syntax.n  in
                   (uu____11810, uu____11814)  in
                 (match uu____11805 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11824))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11830 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11837)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11862 when head_redex env head2 ->
                 let uu____11875 = whnf env phi1  in
                 encode_formula uu____11875 env
             | uu____11876 ->
                 let uu____11889 = encode_term phi1 env  in
                 (match uu____11889 with
                  | (tt,decls) ->
                      let uu____11900 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___116_11903 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___116_11903.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___116_11903.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____11900, decls)))
        | uu____11904 ->
            let uu____11905 = encode_term phi1 env  in
            (match uu____11905 with
             | (tt,decls) ->
                 let uu____11916 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___117_11919 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___117_11919.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___117_11919.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____11916, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____11955 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____11955 with
        | (vars,guards,env2,decls,uu____11994) ->
            let uu____12007 =
              let uu____12020 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12072 =
                          let uu____12083 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12123  ->
                                    match uu____12123 with
                                    | (t,uu____12137) ->
                                        encode_smt_pattern t
                                          (let uu___118_12143 = env2  in
                                           {
                                             bindings =
                                               (uu___118_12143.bindings);
                                             depth = (uu___118_12143.depth);
                                             tcenv = (uu___118_12143.tcenv);
                                             warn = (uu___118_12143.warn);
                                             cache = (uu___118_12143.cache);
                                             nolabels =
                                               (uu___118_12143.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___118_12143.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___118_12143.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12083 FStar_List.unzip
                           in
                        match uu____12072 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12020 FStar_List.unzip  in
            (match uu____12007 with
             | (pats,decls') ->
                 let uu____12252 = encode_formula body env2  in
                 (match uu____12252 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12284;
                             FStar_SMTEncoding_Term.rng = uu____12285;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12300 -> guards  in
                      let uu____12305 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12305, body1,
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
                (fun uu____12365  ->
                   match uu____12365 with
                   | (x,uu____12371) ->
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
               let uu____12379 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12391 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12391) uu____12379 tl1
                in
             let uu____12394 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12421  ->
                       match uu____12421 with
                       | (b,uu____12427) ->
                           let uu____12428 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12428))
                in
             (match uu____12394 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12434) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12448 =
                    let uu____12453 =
                      let uu____12454 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12454
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12453)
                     in
                  FStar_Errors.log_issue pos uu____12448)
          in
       let uu____12455 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12455 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12464 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12522  ->
                     match uu____12522 with
                     | (l,uu____12536) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12464 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12569,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12609 = encode_q_body env vars pats body  in
             match uu____12609 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12654 =
                     let uu____12665 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12665)  in
                   FStar_SMTEncoding_Term.mkForall uu____12654
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12684 = encode_q_body env vars pats body  in
             match uu____12684 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12728 =
                   let uu____12729 =
                     let uu____12740 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12740)  in
                   FStar_SMTEncoding_Term.mkExists uu____12729
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____12728, decls))))

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
  let uu____12843 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____12843 with
  | (asym,a) ->
      let uu____12850 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____12850 with
       | (xsym,x) ->
           let uu____12857 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____12857 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____12905 =
                      let uu____12916 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____12916, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12905  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____12942 =
                      let uu____12949 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____12949)  in
                    FStar_SMTEncoding_Util.mkApp uu____12942  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____12962 =
                    let uu____12965 =
                      let uu____12968 =
                        let uu____12971 =
                          let uu____12972 =
                            let uu____12979 =
                              let uu____12980 =
                                let uu____12991 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____12991)  in
                              FStar_SMTEncoding_Util.mkForall uu____12980  in
                            (uu____12979, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____12972  in
                        let uu____13008 =
                          let uu____13011 =
                            let uu____13012 =
                              let uu____13019 =
                                let uu____13020 =
                                  let uu____13031 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13031)  in
                                FStar_SMTEncoding_Util.mkForall uu____13020
                                 in
                              (uu____13019,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13012  in
                          [uu____13011]  in
                        uu____12971 :: uu____13008  in
                      xtok_decl :: uu____12968  in
                    xname_decl :: uu____12965  in
                  (xtok1, (FStar_List.length vars), uu____12962)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13128 =
                    let uu____13143 =
                      let uu____13154 =
                        let uu____13155 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13155
                         in
                      quant axy uu____13154  in
                    (FStar_Parser_Const.op_Eq, uu____13143)  in
                  let uu____13166 =
                    let uu____13183 =
                      let uu____13198 =
                        let uu____13209 =
                          let uu____13210 =
                            let uu____13211 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13211  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13210
                           in
                        quant axy uu____13209  in
                      (FStar_Parser_Const.op_notEq, uu____13198)  in
                    let uu____13222 =
                      let uu____13239 =
                        let uu____13254 =
                          let uu____13265 =
                            let uu____13266 =
                              let uu____13267 =
                                let uu____13272 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13273 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13272, uu____13273)  in
                              FStar_SMTEncoding_Util.mkLT uu____13267  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13266
                             in
                          quant xy uu____13265  in
                        (FStar_Parser_Const.op_LT, uu____13254)  in
                      let uu____13284 =
                        let uu____13301 =
                          let uu____13316 =
                            let uu____13327 =
                              let uu____13328 =
                                let uu____13329 =
                                  let uu____13334 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13335 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13334, uu____13335)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13329  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13328
                               in
                            quant xy uu____13327  in
                          (FStar_Parser_Const.op_LTE, uu____13316)  in
                        let uu____13346 =
                          let uu____13363 =
                            let uu____13378 =
                              let uu____13389 =
                                let uu____13390 =
                                  let uu____13391 =
                                    let uu____13396 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13397 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13396, uu____13397)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13391  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13390
                                 in
                              quant xy uu____13389  in
                            (FStar_Parser_Const.op_GT, uu____13378)  in
                          let uu____13408 =
                            let uu____13425 =
                              let uu____13440 =
                                let uu____13451 =
                                  let uu____13452 =
                                    let uu____13453 =
                                      let uu____13458 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13459 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13458, uu____13459)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13453
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13452
                                   in
                                quant xy uu____13451  in
                              (FStar_Parser_Const.op_GTE, uu____13440)  in
                            let uu____13470 =
                              let uu____13487 =
                                let uu____13502 =
                                  let uu____13513 =
                                    let uu____13514 =
                                      let uu____13515 =
                                        let uu____13520 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13521 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13520, uu____13521)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13515
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13514
                                     in
                                  quant xy uu____13513  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13502)
                                 in
                              let uu____13532 =
                                let uu____13549 =
                                  let uu____13564 =
                                    let uu____13575 =
                                      let uu____13576 =
                                        let uu____13577 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13577
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13576
                                       in
                                    quant qx uu____13575  in
                                  (FStar_Parser_Const.op_Minus, uu____13564)
                                   in
                                let uu____13588 =
                                  let uu____13605 =
                                    let uu____13620 =
                                      let uu____13631 =
                                        let uu____13632 =
                                          let uu____13633 =
                                            let uu____13638 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____13639 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____13638, uu____13639)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13633
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13632
                                         in
                                      quant xy uu____13631  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13620)
                                     in
                                  let uu____13650 =
                                    let uu____13667 =
                                      let uu____13682 =
                                        let uu____13693 =
                                          let uu____13694 =
                                            let uu____13695 =
                                              let uu____13700 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____13701 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____13700, uu____13701)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13695
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13694
                                           in
                                        quant xy uu____13693  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13682)
                                       in
                                    let uu____13712 =
                                      let uu____13729 =
                                        let uu____13744 =
                                          let uu____13755 =
                                            let uu____13756 =
                                              let uu____13757 =
                                                let uu____13762 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____13763 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____13762, uu____13763)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13757
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13756
                                             in
                                          quant xy uu____13755  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13744)
                                         in
                                      let uu____13774 =
                                        let uu____13791 =
                                          let uu____13806 =
                                            let uu____13817 =
                                              let uu____13818 =
                                                let uu____13819 =
                                                  let uu____13824 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____13825 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____13824, uu____13825)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13819
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13818
                                               in
                                            quant xy uu____13817  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13806)
                                           in
                                        let uu____13836 =
                                          let uu____13853 =
                                            let uu____13868 =
                                              let uu____13879 =
                                                let uu____13880 =
                                                  let uu____13881 =
                                                    let uu____13886 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____13887 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____13886,
                                                      uu____13887)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13881
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13880
                                                 in
                                              quant xy uu____13879  in
                                            (FStar_Parser_Const.op_And,
                                              uu____13868)
                                             in
                                          let uu____13898 =
                                            let uu____13915 =
                                              let uu____13930 =
                                                let uu____13941 =
                                                  let uu____13942 =
                                                    let uu____13943 =
                                                      let uu____13948 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____13949 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____13948,
                                                        uu____13949)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13943
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13942
                                                   in
                                                quant xy uu____13941  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13930)
                                               in
                                            let uu____13960 =
                                              let uu____13977 =
                                                let uu____13992 =
                                                  let uu____14003 =
                                                    let uu____14004 =
                                                      let uu____14005 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14005
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14004
                                                     in
                                                  quant qx uu____14003  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____13992)
                                                 in
                                              [uu____13977]  in
                                            uu____13915 :: uu____13960  in
                                          uu____13853 :: uu____13898  in
                                        uu____13791 :: uu____13836  in
                                      uu____13729 :: uu____13774  in
                                    uu____13667 :: uu____13712  in
                                  uu____13605 :: uu____13650  in
                                uu____13549 :: uu____13588  in
                              uu____13487 :: uu____13532  in
                            uu____13425 :: uu____13470  in
                          uu____13363 :: uu____13408  in
                        uu____13301 :: uu____13346  in
                      uu____13239 :: uu____13284  in
                    uu____13183 :: uu____13222  in
                  uu____13128 :: uu____13166  in
                let mk1 l v1 =
                  let uu____14255 =
                    let uu____14266 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14332  ->
                              match uu____14332 with
                              | (l',uu____14348) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14266
                      (FStar_Option.map
                         (fun uu____14420  ->
                            match uu____14420 with | (uu____14443,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14255 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14528  ->
                          match uu____14528 with
                          | (l',uu____14544) -> FStar_Ident.lid_equals l l'))
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
        let uu____14586 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14586 with
        | (xxsym,xx) ->
            let uu____14593 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14593 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14603 =
                   let uu____14610 =
                     let uu____14611 =
                       let uu____14622 =
                         let uu____14623 =
                           let uu____14628 =
                             let uu____14629 =
                               let uu____14634 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14634)  in
                             FStar_SMTEncoding_Util.mkEq uu____14629  in
                           (xx_has_type, uu____14628)  in
                         FStar_SMTEncoding_Util.mkImp uu____14623  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14622)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14611  in
                   let uu____14659 =
                     let uu____14660 =
                       let uu____14661 =
                         let uu____14662 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14662  in
                       Prims.strcat module_name uu____14661  in
                     varops.mk_unique uu____14660  in
                   (uu____14610, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14659)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14603)
  
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
    let uu____14698 =
      let uu____14699 =
        let uu____14706 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14706, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14699  in
    let uu____14709 =
      let uu____14712 =
        let uu____14713 =
          let uu____14720 =
            let uu____14721 =
              let uu____14732 =
                let uu____14733 =
                  let uu____14738 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____14738)  in
                FStar_SMTEncoding_Util.mkImp uu____14733  in
              ([[typing_pred]], [xx], uu____14732)  in
            mkForall_fuel uu____14721  in
          (uu____14720, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14713  in
      [uu____14712]  in
    uu____14698 :: uu____14709  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____14780 =
      let uu____14781 =
        let uu____14788 =
          let uu____14789 =
            let uu____14800 =
              let uu____14805 =
                let uu____14808 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____14808]  in
              [uu____14805]  in
            let uu____14813 =
              let uu____14814 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14814 tt  in
            (uu____14800, [bb], uu____14813)  in
          FStar_SMTEncoding_Util.mkForall uu____14789  in
        (uu____14788, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14781  in
    let uu____14835 =
      let uu____14838 =
        let uu____14839 =
          let uu____14846 =
            let uu____14847 =
              let uu____14858 =
                let uu____14859 =
                  let uu____14864 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____14864)  in
                FStar_SMTEncoding_Util.mkImp uu____14859  in
              ([[typing_pred]], [xx], uu____14858)  in
            mkForall_fuel uu____14847  in
          (uu____14846, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14839  in
      [uu____14838]  in
    uu____14780 :: uu____14835  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____14914 =
        let uu____14915 =
          let uu____14922 =
            let uu____14925 =
              let uu____14928 =
                let uu____14931 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____14932 =
                  let uu____14935 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____14935]  in
                uu____14931 :: uu____14932  in
              tt :: uu____14928  in
            tt :: uu____14925  in
          ("Prims.Precedes", uu____14922)  in
        FStar_SMTEncoding_Util.mkApp uu____14915  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14914  in
    let precedes_y_x =
      let uu____14939 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14939  in
    let uu____14942 =
      let uu____14943 =
        let uu____14950 =
          let uu____14951 =
            let uu____14962 =
              let uu____14967 =
                let uu____14970 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____14970]  in
              [uu____14967]  in
            let uu____14975 =
              let uu____14976 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14976 tt  in
            (uu____14962, [bb], uu____14975)  in
          FStar_SMTEncoding_Util.mkForall uu____14951  in
        (uu____14950, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14943  in
    let uu____14997 =
      let uu____15000 =
        let uu____15001 =
          let uu____15008 =
            let uu____15009 =
              let uu____15020 =
                let uu____15021 =
                  let uu____15026 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15026)  in
                FStar_SMTEncoding_Util.mkImp uu____15021  in
              ([[typing_pred]], [xx], uu____15020)  in
            mkForall_fuel uu____15009  in
          (uu____15008, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15001  in
      let uu____15051 =
        let uu____15054 =
          let uu____15055 =
            let uu____15062 =
              let uu____15063 =
                let uu____15074 =
                  let uu____15075 =
                    let uu____15080 =
                      let uu____15081 =
                        let uu____15084 =
                          let uu____15087 =
                            let uu____15090 =
                              let uu____15091 =
                                let uu____15096 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15097 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15096, uu____15097)  in
                              FStar_SMTEncoding_Util.mkGT uu____15091  in
                            let uu____15098 =
                              let uu____15101 =
                                let uu____15102 =
                                  let uu____15107 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15108 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15107, uu____15108)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15102  in
                              let uu____15109 =
                                let uu____15112 =
                                  let uu____15113 =
                                    let uu____15118 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15119 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15118, uu____15119)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15113  in
                                [uu____15112]  in
                              uu____15101 :: uu____15109  in
                            uu____15090 :: uu____15098  in
                          typing_pred_y :: uu____15087  in
                        typing_pred :: uu____15084  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15081  in
                    (uu____15080, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15075  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15074)
                 in
              mkForall_fuel uu____15063  in
            (uu____15062,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15055  in
        [uu____15054]  in
      uu____15000 :: uu____15051  in
    uu____14942 :: uu____14997  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15165 =
      let uu____15166 =
        let uu____15173 =
          let uu____15174 =
            let uu____15185 =
              let uu____15190 =
                let uu____15193 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15193]  in
              [uu____15190]  in
            let uu____15198 =
              let uu____15199 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15199 tt  in
            (uu____15185, [bb], uu____15198)  in
          FStar_SMTEncoding_Util.mkForall uu____15174  in
        (uu____15173, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15166  in
    let uu____15220 =
      let uu____15223 =
        let uu____15224 =
          let uu____15231 =
            let uu____15232 =
              let uu____15243 =
                let uu____15244 =
                  let uu____15249 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15249)  in
                FStar_SMTEncoding_Util.mkImp uu____15244  in
              ([[typing_pred]], [xx], uu____15243)  in
            mkForall_fuel uu____15232  in
          (uu____15231, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15224  in
      [uu____15223]  in
    uu____15165 :: uu____15220  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15302 =
      let uu____15303 =
        let uu____15310 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15310, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15303  in
    [uu____15302]  in
  let mk_and_interp env conj uu____15322 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15347 =
      let uu____15348 =
        let uu____15355 =
          let uu____15356 =
            let uu____15367 =
              let uu____15368 =
                let uu____15373 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15373, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15368  in
            ([[l_and_a_b]], [aa; bb], uu____15367)  in
          FStar_SMTEncoding_Util.mkForall uu____15356  in
        (uu____15355, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15348  in
    [uu____15347]  in
  let mk_or_interp env disj uu____15411 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15436 =
      let uu____15437 =
        let uu____15444 =
          let uu____15445 =
            let uu____15456 =
              let uu____15457 =
                let uu____15462 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15462, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15457  in
            ([[l_or_a_b]], [aa; bb], uu____15456)  in
          FStar_SMTEncoding_Util.mkForall uu____15445  in
        (uu____15444, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15437  in
    [uu____15436]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15525 =
      let uu____15526 =
        let uu____15533 =
          let uu____15534 =
            let uu____15545 =
              let uu____15546 =
                let uu____15551 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15551, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15546  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15545)  in
          FStar_SMTEncoding_Util.mkForall uu____15534  in
        (uu____15533, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15526  in
    [uu____15525]  in
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
    let uu____15624 =
      let uu____15625 =
        let uu____15632 =
          let uu____15633 =
            let uu____15644 =
              let uu____15645 =
                let uu____15650 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15650, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15645  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15644)  in
          FStar_SMTEncoding_Util.mkForall uu____15633  in
        (uu____15632, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15625  in
    [uu____15624]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15721 =
      let uu____15722 =
        let uu____15729 =
          let uu____15730 =
            let uu____15741 =
              let uu____15742 =
                let uu____15747 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____15747, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15742  in
            ([[l_imp_a_b]], [aa; bb], uu____15741)  in
          FStar_SMTEncoding_Util.mkForall uu____15730  in
        (uu____15729, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15722  in
    [uu____15721]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15810 =
      let uu____15811 =
        let uu____15818 =
          let uu____15819 =
            let uu____15830 =
              let uu____15831 =
                let uu____15836 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____15836, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15831  in
            ([[l_iff_a_b]], [aa; bb], uu____15830)  in
          FStar_SMTEncoding_Util.mkForall uu____15819  in
        (uu____15818, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15811  in
    [uu____15810]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____15888 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15888  in
    let uu____15891 =
      let uu____15892 =
        let uu____15899 =
          let uu____15900 =
            let uu____15911 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____15911)  in
          FStar_SMTEncoding_Util.mkForall uu____15900  in
        (uu____15899, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15892  in
    [uu____15891]  in
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
      let uu____15971 =
        let uu____15978 =
          let uu____15981 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____15981]  in
        ("Valid", uu____15978)  in
      FStar_SMTEncoding_Util.mkApp uu____15971  in
    let uu____15984 =
      let uu____15985 =
        let uu____15992 =
          let uu____15993 =
            let uu____16004 =
              let uu____16005 =
                let uu____16010 =
                  let uu____16011 =
                    let uu____16022 =
                      let uu____16027 =
                        let uu____16030 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16030]  in
                      [uu____16027]  in
                    let uu____16035 =
                      let uu____16036 =
                        let uu____16041 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16041, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16036  in
                    (uu____16022, [xx1], uu____16035)  in
                  FStar_SMTEncoding_Util.mkForall uu____16011  in
                (uu____16010, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16005  in
            ([[l_forall_a_b]], [aa; bb], uu____16004)  in
          FStar_SMTEncoding_Util.mkForall uu____15993  in
        (uu____15992, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15985  in
    [uu____15984]  in
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
      let uu____16123 =
        let uu____16130 =
          let uu____16133 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16133]  in
        ("Valid", uu____16130)  in
      FStar_SMTEncoding_Util.mkApp uu____16123  in
    let uu____16136 =
      let uu____16137 =
        let uu____16144 =
          let uu____16145 =
            let uu____16156 =
              let uu____16157 =
                let uu____16162 =
                  let uu____16163 =
                    let uu____16174 =
                      let uu____16179 =
                        let uu____16182 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16182]  in
                      [uu____16179]  in
                    let uu____16187 =
                      let uu____16188 =
                        let uu____16193 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16193, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16188  in
                    (uu____16174, [xx1], uu____16187)  in
                  FStar_SMTEncoding_Util.mkExists uu____16163  in
                (uu____16162, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16157  in
            ([[l_exists_a_b]], [aa; bb], uu____16156)  in
          FStar_SMTEncoding_Util.mkForall uu____16145  in
        (uu____16144, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16137  in
    [uu____16136]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16253 =
      let uu____16254 =
        let uu____16261 =
          let uu____16262 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16262 range_ty  in
        let uu____16263 = varops.mk_unique "typing_range_const"  in
        (uu____16261, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16263)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16254  in
    [uu____16253]  in
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
        let uu____16297 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16297 x1 t  in
      let uu____16298 =
        let uu____16309 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16309)  in
      FStar_SMTEncoding_Util.mkForall uu____16298  in
    let uu____16332 =
      let uu____16333 =
        let uu____16340 =
          let uu____16341 =
            let uu____16352 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16352)  in
          FStar_SMTEncoding_Util.mkForall uu____16341  in
        (uu____16340,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16333  in
    [uu____16332]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____16402 =
      let uu____16403 =
        let uu____16410 =
          let uu____16411 =
            let uu____16426 =
              let uu____16427 =
                let uu____16432 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____16433 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____16432, uu____16433)  in
              FStar_SMTEncoding_Util.mkAnd uu____16427  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16426)
             in
          FStar_SMTEncoding_Util.mkForall' uu____16411  in
        (uu____16410,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16403  in
    [uu____16402]  in
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
          let uu____16779 =
            FStar_Util.find_opt
              (fun uu____16805  ->
                 match uu____16805 with
                 | (l,uu____16817) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16779 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16842,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16878 = encode_function_type_as_formula t env  in
        match uu____16878 with
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
              let uu____16918 =
                ((let uu____16921 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____16921) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____16918
              then
                let arg_sorts =
                  let uu____16931 =
                    let uu____16932 = FStar_Syntax_Subst.compress t_norm  in
                    uu____16932.FStar_Syntax_Syntax.n  in
                  match uu____16931 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16938) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____16968  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____16973 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____16975 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____16975 with
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
                (let uu____17008 = prims.is lid  in
                 if uu____17008
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17016 = prims.mk lid vname  in
                   match uu____17016 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17043 =
                      let uu____17054 = curried_arrow_formals_comp t_norm  in
                      match uu____17054 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17072 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17072
                            then
                              let uu____17073 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___119_17076 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___119_17076.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___119_17076.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___119_17076.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___119_17076.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___119_17076.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___119_17076.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___119_17076.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___119_17076.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___119_17076.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___119_17076.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___119_17076.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___119_17076.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___119_17076.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___119_17076.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___119_17076.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___119_17076.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___119_17076.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___119_17076.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___119_17076.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___119_17076.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___119_17076.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___119_17076.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___119_17076.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___119_17076.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___119_17076.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___119_17076.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___119_17076.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___119_17076.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___119_17076.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___119_17076.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___119_17076.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___119_17076.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___119_17076.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___119_17076.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17073
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17088 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17088)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17043 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____17138 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____17138 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17163 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___91_17205  ->
                                       match uu___91_17205 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17209 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17209 with
                                            | (uu____17230,(xxsym,uu____17232))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17250 =
                                                  let uu____17251 =
                                                    let uu____17258 =
                                                      let uu____17259 =
                                                        let uu____17270 =
                                                          let uu____17271 =
                                                            let uu____17276 =
                                                              let uu____17277
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17277
                                                               in
                                                            (vapp,
                                                              uu____17276)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17271
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17270)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17259
                                                       in
                                                    (uu____17258,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17251
                                                   in
                                                [uu____17250])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17296 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17296 with
                                            | (uu____17317,(xxsym,uu____17319))
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
                                                let uu____17342 =
                                                  let uu____17343 =
                                                    let uu____17350 =
                                                      let uu____17351 =
                                                        let uu____17362 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17362)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17351
                                                       in
                                                    (uu____17350,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17343
                                                   in
                                                [uu____17342])
                                       | uu____17379 -> []))
                                in
                             let uu____17380 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17380 with
                              | (vars,guards,env',decls1,uu____17407) ->
                                  let uu____17420 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17429 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17429, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17431 =
                                          encode_formula p env'  in
                                        (match uu____17431 with
                                         | (g,ds) ->
                                             let uu____17442 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17442,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17420 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17455 =
                                           let uu____17462 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17462)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17455
                                          in
                                       let uu____17471 =
                                         let vname_decl =
                                           let uu____17479 =
                                             let uu____17490 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17500  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17490,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17479
                                            in
                                         let uu____17509 =
                                           let env2 =
                                             let uu___120_17515 = env1  in
                                             {
                                               bindings =
                                                 (uu___120_17515.bindings);
                                               depth = (uu___120_17515.depth);
                                               tcenv = (uu___120_17515.tcenv);
                                               warn = (uu___120_17515.warn);
                                               cache = (uu___120_17515.cache);
                                               nolabels =
                                                 (uu___120_17515.nolabels);
                                               use_zfuel_name =
                                                 (uu___120_17515.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___120_17515.current_module_name)
                                             }  in
                                           let uu____17516 =
                                             let uu____17517 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17517
                                              in
                                           if uu____17516
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17509 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17532::uu____17533 ->
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
                                                     let uu____17573 =
                                                       let uu____17584 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17584)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17573
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17611 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17614 =
                                               match formals with
                                               | [] ->
                                                   let uu____17631 =
                                                     let uu____17632 =
                                                       let uu____17635 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17635
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____17632
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17631)
                                               | uu____17644 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17651 =
                                                       let uu____17658 =
                                                         let uu____17659 =
                                                           let uu____17670 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17670)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17659
                                                          in
                                                       (uu____17658,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17651
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17614 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17471 with
                                        | (decls2,env2) ->
                                            let uu____17713 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17721 =
                                                encode_term res_t1 env'  in
                                              match uu____17721 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17734 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17734, decls)
                                               in
                                            (match uu____17713 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17745 =
                                                     let uu____17752 =
                                                       let uu____17753 =
                                                         let uu____17764 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17764)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17753
                                                        in
                                                     (uu____17752,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17745
                                                    in
                                                 let freshness =
                                                   let uu____17780 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17780
                                                   then
                                                     let uu____17785 =
                                                       let uu____17786 =
                                                         let uu____17797 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17808 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17797,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17808)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17786
                                                        in
                                                     let uu____17811 =
                                                       let uu____17814 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17814]  in
                                                     uu____17785 ::
                                                       uu____17811
                                                   else []  in
                                                 let g =
                                                   let uu____17819 =
                                                     let uu____17822 =
                                                       let uu____17825 =
                                                         let uu____17828 =
                                                           let uu____17831 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17831
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17828
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17825
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17822
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17819
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
          let uu____17856 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____17856 with
          | FStar_Pervasives_Native.None  ->
              let uu____17867 = encode_free_var false env x t t_norm []  in
              (match uu____17867 with
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
            let uu____17920 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____17920 with
            | (decls,env1) ->
                let uu____17939 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____17939
                then
                  let uu____17946 =
                    let uu____17949 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____17949  in
                  (uu____17946, env1)
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
             (fun uu____18001  ->
                fun lb  ->
                  match uu____18001 with
                  | (decls,env1) ->
                      let uu____18021 =
                        let uu____18028 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18028
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18021 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18049 = FStar_Syntax_Util.head_and_args t  in
    match uu____18049 with
    | (hd1,args) ->
        let uu____18086 =
          let uu____18087 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18087.FStar_Syntax_Syntax.n  in
        (match uu____18086 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18091,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18110 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18132  ->
      fun quals  ->
        match uu____18132 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18208 = FStar_Util.first_N nbinders formals  in
              match uu____18208 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18289  ->
                         fun uu____18290  ->
                           match (uu____18289, uu____18290) with
                           | ((formal,uu____18308),(binder,uu____18310)) ->
                               let uu____18319 =
                                 let uu____18326 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18326)  in
                               FStar_Syntax_Syntax.NT uu____18319) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18334 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18365  ->
                              match uu____18365 with
                              | (x,i) ->
                                  let uu____18376 =
                                    let uu___121_18377 = x  in
                                    let uu____18378 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_18377.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_18377.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18378
                                    }  in
                                  (uu____18376, i)))
                       in
                    FStar_All.pipe_right uu____18334
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18396 =
                      let uu____18397 = FStar_Syntax_Subst.compress body  in
                      let uu____18398 =
                        let uu____18399 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18399
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18397
                        uu____18398
                       in
                    uu____18396 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18460 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18460
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___122_18463 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_18463.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_18463.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_18463.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_18463.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_18463.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_18463.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_18463.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_18463.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_18463.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_18463.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_18463.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_18463.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_18463.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_18463.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_18463.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_18463.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_18463.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_18463.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_18463.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___122_18463.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___122_18463.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___122_18463.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_18463.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_18463.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___122_18463.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_18463.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_18463.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___122_18463.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___122_18463.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_18463.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___122_18463.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___122_18463.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___122_18463.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___122_18463.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18496 = FStar_Syntax_Util.abs_formals e  in
                match uu____18496 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18560::uu____18561 ->
                         let uu____18576 =
                           let uu____18577 =
                             let uu____18580 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18580
                              in
                           uu____18577.FStar_Syntax_Syntax.n  in
                         (match uu____18576 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18623 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18623 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18665 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18665
                                   then
                                     let uu____18700 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18700 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18794  ->
                                                   fun uu____18795  ->
                                                     match (uu____18794,
                                                             uu____18795)
                                                     with
                                                     | ((x,uu____18813),
                                                        (b,uu____18815)) ->
                                                         let uu____18824 =
                                                           let uu____18831 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____18831)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18824)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____18833 =
                                            let uu____18854 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____18854)
                                             in
                                          (uu____18833, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18922 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____18922 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19011) ->
                              let uu____19016 =
                                let uu____19037 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19037  in
                              (uu____19016, true)
                          | uu____19102 when Prims.op_Negation norm1 ->
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
                          | uu____19104 ->
                              let uu____19105 =
                                let uu____19106 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19107 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19106
                                  uu____19107
                                 in
                              failwith uu____19105)
                     | uu____19132 ->
                         let rec aux' t_norm2 =
                           let uu____19157 =
                             let uu____19158 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19158.FStar_Syntax_Syntax.n  in
                           match uu____19157 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19199 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19199 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19227 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19227 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19307)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19312 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19368 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19368
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19380 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19443  ->
                            fun lb  ->
                              match uu____19443 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19498 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19498
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19501 =
                                      let uu____19510 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19510
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19501 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19380 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____19630 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19638 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____19638 vars)
                            else
                              (let uu____19640 =
                                 let uu____19647 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____19647)  in
                               FStar_SMTEncoding_Util.mkApp uu____19640)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19699;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19701;
                             FStar_Syntax_Syntax.lbeff = uu____19702;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____19704;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____19728 =
                              let uu____19735 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____19735 with
                              | (tcenv',uu____19753,e_t) ->
                                  let uu____19759 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19770 -> failwith "Impossible"
                                     in
                                  (match uu____19759 with
                                   | (e1,t_norm1) ->
                                       ((let uu___125_19786 = env2  in
                                         {
                                           bindings =
                                             (uu___125_19786.bindings);
                                           depth = (uu___125_19786.depth);
                                           tcenv = tcenv';
                                           warn = (uu___125_19786.warn);
                                           cache = (uu___125_19786.cache);
                                           nolabels =
                                             (uu___125_19786.nolabels);
                                           use_zfuel_name =
                                             (uu___125_19786.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___125_19786.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___125_19786.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____19728 with
                             | (env',e1,t_norm1) ->
                                 let uu____19796 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____19796 with
                                  | ((binders,body,uu____19817,t_body),curry)
                                      ->
                                      ((let uu____19829 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____19829
                                        then
                                          let uu____19830 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____19831 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____19830 uu____19831
                                        else ());
                                       (let uu____19833 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____19833 with
                                        | (vars,guards,env'1,binder_decls,uu____19860)
                                            ->
                                            let body1 =
                                              let uu____19874 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____19874
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
                                              mk_app1 curry fvb.smt_id
                                                fvb.smt_token vars
                                               in
                                            let uu____19891 =
                                              let uu____19900 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____19900
                                              then
                                                let uu____19911 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____19912 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____19911, uu____19912)
                                              else
                                                (let uu____19922 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____19922))
                                               in
                                            (match uu____19891 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____19945 =
                                                     let uu____19952 =
                                                       let uu____19953 =
                                                         let uu____19964 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____19964)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____19953
                                                        in
                                                     let uu____19975 =
                                                       let uu____19978 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____19978
                                                        in
                                                     (uu____19952,
                                                       uu____19975,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____19945
                                                    in
                                                 let uu____19981 =
                                                   let uu____19984 =
                                                     let uu____19987 =
                                                       let uu____19990 =
                                                         let uu____19993 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____19993
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____19990
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____19987
                                                      in
                                                   FStar_List.append decls1
                                                     uu____19984
                                                    in
                                                 (uu____19981, env2))))))
                        | uu____19998 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____20053 = varops.fresh "fuel"  in
                          (uu____20053, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____20056 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____20103  ->
                                  fun fvb  ->
                                    match uu____20103 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____20149 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____20149  in
                                        let gtok =
                                          let uu____20151 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____20151  in
                                        let env4 =
                                          let uu____20153 =
                                            let uu____20156 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_42  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_42) uu____20156
                                             in
                                          push_free_var env3 flid
                                            (fvb.smt_arity +
                                               (Prims.parse_int "1")) gtok
                                            uu____20153
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____20056 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____20256 t_norm
                              uu____20258 =
                              match (uu____20256, uu____20258) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____20288;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____20289;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____20291;_})
                                  ->
                                  let uu____20312 =
                                    let uu____20319 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____20319 with
                                    | (tcenv',uu____20341,e_t) ->
                                        let uu____20347 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20358 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____20347 with
                                         | (e1,t_norm1) ->
                                             ((let uu___126_20374 = env3  in
                                               {
                                                 bindings =
                                                   (uu___126_20374.bindings);
                                                 depth =
                                                   (uu___126_20374.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___126_20374.warn);
                                                 cache =
                                                   (uu___126_20374.cache);
                                                 nolabels =
                                                   (uu___126_20374.nolabels);
                                                 use_zfuel_name =
                                                   (uu___126_20374.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___126_20374.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___126_20374.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____20312 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20389 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____20389
                                         then
                                           let uu____20390 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____20391 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____20392 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20390 uu____20391
                                             uu____20392
                                         else ());
                                        (let uu____20394 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____20394 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20431 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____20431
                                               then
                                                 let uu____20432 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____20433 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____20434 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____20435 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20432 uu____20433
                                                   uu____20434 uu____20435
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20439 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____20439 with
                                               | (vars,guards,env'1,binder_decls,uu____20470)
                                                   ->
                                                   let decl_g =
                                                     let uu____20484 =
                                                       let uu____20495 =
                                                         let uu____20498 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20498
                                                          in
                                                       (g, uu____20495,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20484
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
                                                     let uu____20523 =
                                                       let uu____20530 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____20530)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20523
                                                      in
                                                   let gsapp =
                                                     let uu____20540 =
                                                       let uu____20547 =
                                                         let uu____20550 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____20550 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20547)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20540
                                                      in
                                                   let gmax =
                                                     let uu____20556 =
                                                       let uu____20563 =
                                                         let uu____20566 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____20566 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20563)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20556
                                                      in
                                                   let body1 =
                                                     let uu____20572 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____20572
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____20574 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____20574 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____20592 =
                                                            let uu____20599 =
                                                              let uu____20600
                                                                =
                                                                let uu____20615
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
                                                                  uu____20615)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20600
                                                               in
                                                            let uu____20636 =
                                                              let uu____20639
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20639
                                                               in
                                                            (uu____20599,
                                                              uu____20636,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20592
                                                           in
                                                        let eqn_f =
                                                          let uu____20643 =
                                                            let uu____20650 =
                                                              let uu____20651
                                                                =
                                                                let uu____20662
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20662)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20651
                                                               in
                                                            (uu____20650,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20643
                                                           in
                                                        let eqn_g' =
                                                          let uu____20676 =
                                                            let uu____20683 =
                                                              let uu____20684
                                                                =
                                                                let uu____20695
                                                                  =
                                                                  let uu____20696
                                                                    =
                                                                    let uu____20701
                                                                    =
                                                                    let uu____20702
                                                                    =
                                                                    let uu____20709
                                                                    =
                                                                    let uu____20712
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____20712
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____20709)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20702
                                                                     in
                                                                    (gsapp,
                                                                    uu____20701)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____20696
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20695)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20684
                                                               in
                                                            (uu____20683,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20676
                                                           in
                                                        let uu____20735 =
                                                          let uu____20744 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____20744
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____20773)
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
                                                                  let uu____20798
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____20798
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____20803
                                                                  =
                                                                  let uu____20810
                                                                    =
                                                                    let uu____20811
                                                                    =
                                                                    let uu____20822
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20822)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20811
                                                                     in
                                                                  (uu____20810,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____20803
                                                                 in
                                                              let uu____20843
                                                                =
                                                                let uu____20850
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____20850
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____20863
                                                                    =
                                                                    let uu____20866
                                                                    =
                                                                    let uu____20867
                                                                    =
                                                                    let uu____20874
                                                                    =
                                                                    let uu____20875
                                                                    =
                                                                    let uu____20886
                                                                    =
                                                                    let uu____20887
                                                                    =
                                                                    let uu____20892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____20892,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____20887
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20886)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20875
                                                                     in
                                                                    (uu____20874,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20867
                                                                     in
                                                                    [uu____20866]
                                                                     in
                                                                    (d3,
                                                                    uu____20863)
                                                                 in
                                                              (match uu____20843
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
                                                        (match uu____20735
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
                            let uu____20957 =
                              let uu____20970 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21031  ->
                                   fun uu____21032  ->
                                     match (uu____21031, uu____21032) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21157 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21157 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____20970
                               in
                            (match uu____20957 with
                             | (decls2,eqns,env01) ->
                                 let uu____21230 =
                                   let isDeclFun uu___92_21242 =
                                     match uu___92_21242 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21243 -> true
                                     | uu____21254 -> false  in
                                   let uu____21255 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____21255
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____21230 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____21295 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___93_21299  ->
                                 match uu___93_21299 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21300 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21306 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21306)))
                         in
                      if uu____21295
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
                   let uu____21358 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____21358
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
        let uu____21407 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____21407 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____21411 = encode_sigelt' env se  in
      match uu____21411 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21427 =
                  let uu____21428 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____21428  in
                [uu____21427]
            | uu____21429 ->
                let uu____21430 =
                  let uu____21433 =
                    let uu____21434 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21434  in
                  uu____21433 :: g  in
                let uu____21435 =
                  let uu____21438 =
                    let uu____21439 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21439  in
                  [uu____21438]  in
                FStar_List.append uu____21430 uu____21435
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
        let uu____21452 =
          let uu____21453 = FStar_Syntax_Subst.compress t  in
          uu____21453.FStar_Syntax_Syntax.n  in
        match uu____21452 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21457)) -> s = "opaque_to_smt"
        | uu____21458 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____21463 =
          let uu____21464 = FStar_Syntax_Subst.compress t  in
          uu____21464.FStar_Syntax_Syntax.n  in
        match uu____21463 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21468)) -> s = "uninterpreted_by_smt"
        | uu____21469 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21474 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21479 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21482 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21485 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21500 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21504 =
            let uu____21505 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____21505 Prims.op_Negation  in
          if uu____21504
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____21531 ->
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
               let uu____21551 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____21551 with
               | (formals,uu____21569) ->
                   let arity = FStar_List.length formals  in
                   let uu____21587 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____21587 with
                    | (aname,atok,env2) ->
                        let uu____21607 =
                          let uu____21612 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____21612 env2  in
                        (match uu____21607 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____21624 =
                                 let uu____21625 =
                                   let uu____21636 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21652  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____21636,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____21625
                                  in
                               [uu____21624;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____21665 =
                               let aux uu____21717 uu____21718 =
                                 match (uu____21717, uu____21718) with
                                 | ((bv,uu____21770),(env3,acc_sorts,acc)) ->
                                     let uu____21808 = gen_term_var env3 bv
                                        in
                                     (match uu____21808 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____21665 with
                              | (uu____21880,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____21903 =
                                      let uu____21910 =
                                        let uu____21911 =
                                          let uu____21922 =
                                            let uu____21923 =
                                              let uu____21928 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____21928)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____21923
                                             in
                                          ([[app]], xs_sorts, uu____21922)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____21911
                                         in
                                      (uu____21910,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____21903
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____21948 =
                                      let uu____21955 =
                                        let uu____21956 =
                                          let uu____21967 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____21967)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____21956
                                         in
                                      (uu____21955,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____21948
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____21986 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____21986 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22014,uu____22015)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22016 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____22016 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22033,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22039 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___94_22043  ->
                      match uu___94_22043 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22044 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22049 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22050 -> false))
               in
            Prims.op_Negation uu____22039  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22059 =
               let uu____22066 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22066 env fv t quals  in
             match uu____22059 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22081 =
                   let uu____22084 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22084  in
                 (uu____22081, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22092 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22092 with
           | (uu____22101,f1) ->
               let uu____22103 = encode_formula f1 env  in
               (match uu____22103 with
                | (f2,decls) ->
                    let g =
                      let uu____22117 =
                        let uu____22118 =
                          let uu____22125 =
                            let uu____22128 =
                              let uu____22129 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22129
                               in
                            FStar_Pervasives_Native.Some uu____22128  in
                          let uu____22130 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22125, uu____22130)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22118  in
                      [uu____22117]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22136) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22148 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22166 =
                       let uu____22169 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22169.FStar_Syntax_Syntax.fv_name  in
                     uu____22166.FStar_Syntax_Syntax.v  in
                   let uu____22170 =
                     let uu____22171 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22171  in
                   if uu____22170
                   then
                     let val_decl =
                       let uu___129_22199 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___129_22199.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___129_22199.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___129_22199.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____22204 = encode_sigelt' env1 val_decl  in
                     match uu____22204 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22148 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22232,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22234;
                          FStar_Syntax_Syntax.lbtyp = uu____22235;
                          FStar_Syntax_Syntax.lbeff = uu____22236;
                          FStar_Syntax_Syntax.lbdef = uu____22237;
                          FStar_Syntax_Syntax.lbattrs = uu____22238;_}::[]),uu____22239)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22262 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____22262 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____22291 =
                   let uu____22294 =
                     let uu____22295 =
                       let uu____22302 =
                         let uu____22303 =
                           let uu____22314 =
                             let uu____22315 =
                               let uu____22320 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____22320)  in
                             FStar_SMTEncoding_Util.mkEq uu____22315  in
                           ([[b2t_x]], [xx], uu____22314)  in
                         FStar_SMTEncoding_Util.mkForall uu____22303  in
                       (uu____22302,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____22295  in
                   [uu____22294]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22291
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22353,uu____22354) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_22363  ->
                  match uu___95_22363 with
                  | FStar_Syntax_Syntax.Discriminator uu____22364 -> true
                  | uu____22365 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22368,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22379 =
                     let uu____22380 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____22380.FStar_Ident.idText  in
                   uu____22379 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___96_22384  ->
                     match uu___96_22384 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22385 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22389) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_22406  ->
                  match uu___97_22406 with
                  | FStar_Syntax_Syntax.Projector uu____22407 -> true
                  | uu____22412 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____22415 = try_lookup_free_var env l  in
          (match uu____22415 with
           | FStar_Pervasives_Native.Some uu____22422 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___130_22426 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___130_22426.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___130_22426.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___130_22426.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22433) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22451) ->
          let uu____22460 = encode_sigelts env ses  in
          (match uu____22460 with
           | (g,env1) ->
               let uu____22477 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___98_22500  ->
                         match uu___98_22500 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22501;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22502;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22503;_}
                             -> false
                         | uu____22506 -> true))
                  in
               (match uu____22477 with
                | (g',inversions) ->
                    let uu____22521 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___99_22542  ->
                              match uu___99_22542 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22543 ->
                                  true
                              | uu____22554 -> false))
                       in
                    (match uu____22521 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22572,tps,k,uu____22575,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___100_22592  ->
                    match uu___100_22592 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22593 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22602 = c  in
              match uu____22602 with
              | (name,args,uu____22607,uu____22608,uu____22609) ->
                  let uu____22614 =
                    let uu____22615 =
                      let uu____22626 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22643  ->
                                match uu____22643 with
                                | (uu____22650,sort,uu____22652) -> sort))
                         in
                      (name, uu____22626, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____22615  in
                  [uu____22614]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____22679 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____22685 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____22685 FStar_Option.isNone))
               in
            if uu____22679
            then []
            else
              (let uu____22717 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____22717 with
               | (xxsym,xx) ->
                   let uu____22726 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____22765  ->
                             fun l  ->
                               match uu____22765 with
                               | (out,decls) ->
                                   let uu____22785 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____22785 with
                                    | (uu____22796,data_t) ->
                                        let uu____22798 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____22798 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____22844 =
                                                 let uu____22845 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____22845.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____22844 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____22856,indices) ->
                                                   indices
                                               | uu____22878 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____22902  ->
                                                         match uu____22902
                                                         with
                                                         | (x,uu____22908) ->
                                                             let uu____22909
                                                               =
                                                               let uu____22910
                                                                 =
                                                                 let uu____22917
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____22917,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____22910
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____22909)
                                                    env)
                                                in
                                             let uu____22920 =
                                               encode_args indices env1  in
                                             (match uu____22920 with
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
                                                      let uu____22946 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____22962
                                                                 =
                                                                 let uu____22967
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____22967,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____22962)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____22946
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____22970 =
                                                      let uu____22971 =
                                                        let uu____22976 =
                                                          let uu____22977 =
                                                            let uu____22982 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____22982,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____22977
                                                           in
                                                        (out, uu____22976)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____22971
                                                       in
                                                    (uu____22970,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____22726 with
                    | (data_ax,decls) ->
                        let uu____22995 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____22995 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23006 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23006 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23010 =
                                 let uu____23017 =
                                   let uu____23018 =
                                     let uu____23029 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23044 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23029,
                                       uu____23044)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23018
                                    in
                                 let uu____23059 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23017,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23059)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23010
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23062 =
            let uu____23075 =
              let uu____23076 = FStar_Syntax_Subst.compress k  in
              uu____23076.FStar_Syntax_Syntax.n  in
            match uu____23075 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23121 -> (tps, k)  in
          (match uu____23062 with
           | (formals,res) ->
               let uu____23144 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23144 with
                | (formals1,res1) ->
                    let uu____23155 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23155 with
                     | (vars,guards,env',binder_decls,uu____23180) ->
                         let arity = FStar_List.length vars  in
                         let uu____23194 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____23194 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23217 =
                                  let uu____23224 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23224)  in
                                FStar_SMTEncoding_Util.mkApp uu____23217  in
                              let uu____23233 =
                                let tname_decl =
                                  let uu____23243 =
                                    let uu____23244 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23276  ->
                                              match uu____23276 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23289 = varops.next_id ()  in
                                    (tname, uu____23244,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23289, false)
                                     in
                                  constructor_or_logic_type_decl uu____23243
                                   in
                                let uu____23298 =
                                  match vars with
                                  | [] ->
                                      let uu____23311 =
                                        let uu____23312 =
                                          let uu____23315 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23315
                                           in
                                        push_free_var env1 t arity tname
                                          uu____23312
                                         in
                                      ([], uu____23311)
                                  | uu____23326 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____23335 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23335
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____23349 =
                                          let uu____23356 =
                                            let uu____23357 =
                                              let uu____23372 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23372)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23357
                                             in
                                          (uu____23356,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23349
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____23298 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23233 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23412 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____23412 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23430 =
                                               let uu____23431 =
                                                 let uu____23438 =
                                                   let uu____23439 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23439
                                                    in
                                                 (uu____23438,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23431
                                                in
                                             [uu____23430]
                                           else []  in
                                         let uu____23443 =
                                           let uu____23446 =
                                             let uu____23449 =
                                               let uu____23450 =
                                                 let uu____23457 =
                                                   let uu____23458 =
                                                     let uu____23469 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____23469)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23458
                                                    in
                                                 (uu____23457,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23450
                                                in
                                             [uu____23449]  in
                                           FStar_List.append karr uu____23446
                                            in
                                         FStar_List.append decls1 uu____23443
                                      in
                                   let aux =
                                     let uu____23485 =
                                       let uu____23488 =
                                         inversion_axioms tapp vars  in
                                       let uu____23491 =
                                         let uu____23494 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____23494]  in
                                       FStar_List.append uu____23488
                                         uu____23491
                                        in
                                     FStar_List.append kindingAx uu____23485
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23501,uu____23502,uu____23503,uu____23504,uu____23505)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23513,t,uu____23515,n_tps,uu____23517) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____23525 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____23525 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____23565 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____23565 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____23586 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____23586 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____23600 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____23600 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____23670 =
                                            mk_term_projector_name d x  in
                                          (uu____23670,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____23672 =
                                  let uu____23691 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23691, true)
                                   in
                                FStar_All.pipe_right uu____23672
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
                              let uu____23730 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____23730 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23742::uu____23743 ->
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
                                         let uu____23788 =
                                           let uu____23799 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____23799)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____23788
                                     | uu____23824 -> tok_typing  in
                                   let uu____23833 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____23833 with
                                    | (vars',guards',env'',decls_formals,uu____23858)
                                        ->
                                        let uu____23871 =
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
                                        (match uu____23871 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____23902 ->
                                                   let uu____23909 =
                                                     let uu____23910 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____23910
                                                      in
                                                   [uu____23909]
                                                in
                                             let encode_elim uu____23920 =
                                               let uu____23921 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____23921 with
                                               | (head1,args) ->
                                                   let uu____23964 =
                                                     let uu____23965 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____23965.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____23964 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____23975;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____23976;_},uu____23977)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____23983 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____23983
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____24026
                                                                    ->
                                                                    let uu____24027
                                                                    =
                                                                    let uu____24032
                                                                    =
                                                                    let uu____24033
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24033
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24032)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24027
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24049
                                                                    =
                                                                    let uu____24050
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24050
                                                                     in
                                                                    if
                                                                    uu____24049
                                                                    then
                                                                    let uu____24063
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24063]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____24065
                                                               =
                                                               let uu____24078
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24128
                                                                     ->
                                                                    fun
                                                                    uu____24129
                                                                     ->
                                                                    match 
                                                                    (uu____24128,
                                                                    uu____24129)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24224
                                                                    =
                                                                    let uu____24231
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24231
                                                                     in
                                                                    (match uu____24224
                                                                    with
                                                                    | 
                                                                    (uu____24244,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24252
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24252
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24254
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24254
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 uu____24078
                                                                in
                                                             (match uu____24065
                                                              with
                                                              | (uu____24269,arg_vars,elim_eqns_or_guards,uu____24272)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
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
                                                                    let uu____24302
                                                                    =
                                                                    let uu____24309
                                                                    =
                                                                    let uu____24310
                                                                    =
                                                                    let uu____24321
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24332
                                                                    =
                                                                    let uu____24333
                                                                    =
                                                                    let uu____24338
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24338)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24333
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24321,
                                                                    uu____24332)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24310
                                                                     in
                                                                    (uu____24309,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24302
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24361
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24361,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24363
                                                                    =
                                                                    let uu____24370
                                                                    =
                                                                    let uu____24371
                                                                    =
                                                                    let uu____24382
                                                                    =
                                                                    let uu____24387
                                                                    =
                                                                    let uu____24390
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____24390]
                                                                     in
                                                                    [uu____24387]
                                                                     in
                                                                    let uu____24395
                                                                    =
                                                                    let uu____24396
                                                                    =
                                                                    let uu____24401
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____24402
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____24401,
                                                                    uu____24402)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24396
                                                                     in
                                                                    (uu____24382,
                                                                    [x],
                                                                    uu____24395)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24371
                                                                     in
                                                                    let uu____24421
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24370,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24421)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24363
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24428
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
                                                                    (let uu____24456
                                                                    =
                                                                    let uu____24457
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24457
                                                                    dapp1  in
                                                                    [uu____24456])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24428
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____24464
                                                                    =
                                                                    let uu____24471
                                                                    =
                                                                    let uu____24472
                                                                    =
                                                                    let uu____24483
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24494
                                                                    =
                                                                    let uu____24495
                                                                    =
                                                                    let uu____24500
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____24500)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24495
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24483,
                                                                    uu____24494)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24472
                                                                     in
                                                                    (uu____24471,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24464)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____24521 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____24521
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____24564
                                                                    ->
                                                                    let uu____24565
                                                                    =
                                                                    let uu____24570
                                                                    =
                                                                    let uu____24571
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24571
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24570)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24565
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24587
                                                                    =
                                                                    let uu____24588
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24588
                                                                     in
                                                                    if
                                                                    uu____24587
                                                                    then
                                                                    let uu____24601
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24601]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____24603
                                                               =
                                                               let uu____24616
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24666
                                                                     ->
                                                                    fun
                                                                    uu____24667
                                                                     ->
                                                                    match 
                                                                    (uu____24666,
                                                                    uu____24667)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24762
                                                                    =
                                                                    let uu____24769
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24769
                                                                     in
                                                                    (match uu____24762
                                                                    with
                                                                    | 
                                                                    (uu____24782,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24790
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24790
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24792
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24792
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 uu____24616
                                                                in
                                                             (match uu____24603
                                                              with
                                                              | (uu____24807,arg_vars,elim_eqns_or_guards,uu____24810)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
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
                                                                    let uu____24840
                                                                    =
                                                                    let uu____24847
                                                                    =
                                                                    let uu____24848
                                                                    =
                                                                    let uu____24859
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24870
                                                                    =
                                                                    let uu____24871
                                                                    =
                                                                    let uu____24876
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24876)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24871
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24859,
                                                                    uu____24870)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24848
                                                                     in
                                                                    (uu____24847,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24840
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24899
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24899,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24901
                                                                    =
                                                                    let uu____24908
                                                                    =
                                                                    let uu____24909
                                                                    =
                                                                    let uu____24920
                                                                    =
                                                                    let uu____24925
                                                                    =
                                                                    let uu____24928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____24928]
                                                                     in
                                                                    [uu____24925]
                                                                     in
                                                                    let uu____24933
                                                                    =
                                                                    let uu____24934
                                                                    =
                                                                    let uu____24939
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____24940
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____24939,
                                                                    uu____24940)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24934
                                                                     in
                                                                    (uu____24920,
                                                                    [x],
                                                                    uu____24933)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24909
                                                                     in
                                                                    let uu____24959
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24908,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24959)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24901
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24966
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
                                                                    (let uu____24994
                                                                    =
                                                                    let uu____24995
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24995
                                                                    dapp1  in
                                                                    [uu____24994])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24966
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25002
                                                                    =
                                                                    let uu____25009
                                                                    =
                                                                    let uu____25010
                                                                    =
                                                                    let uu____25021
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25032
                                                                    =
                                                                    let uu____25033
                                                                    =
                                                                    let uu____25038
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25038)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25033
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25021,
                                                                    uu____25032)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25010
                                                                     in
                                                                    (uu____25009,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25002)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25057 ->
                                                        ((let uu____25059 =
                                                            let uu____25064 =
                                                              let uu____25065
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25066
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25065
                                                                uu____25066
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25064)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25059);
                                                         ([], [])))
                                                in
                                             let uu____25071 = encode_elim ()
                                                in
                                             (match uu____25071 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25091 =
                                                      let uu____25094 =
                                                        let uu____25097 =
                                                          let uu____25100 =
                                                            let uu____25103 =
                                                              let uu____25104
                                                                =
                                                                let uu____25115
                                                                  =
                                                                  let uu____25118
                                                                    =
                                                                    let uu____25119
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25119
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25118
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25115)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25104
                                                               in
                                                            [uu____25103]  in
                                                          let uu____25124 =
                                                            let uu____25127 =
                                                              let uu____25130
                                                                =
                                                                let uu____25133
                                                                  =
                                                                  let uu____25136
                                                                    =
                                                                    let uu____25139
                                                                    =
                                                                    let uu____25142
                                                                    =
                                                                    let uu____25143
                                                                    =
                                                                    let uu____25150
                                                                    =
                                                                    let uu____25151
                                                                    =
                                                                    let uu____25162
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25162)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25151
                                                                     in
                                                                    (uu____25150,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25143
                                                                     in
                                                                    let uu____25175
                                                                    =
                                                                    let uu____25178
                                                                    =
                                                                    let uu____25179
                                                                    =
                                                                    let uu____25186
                                                                    =
                                                                    let uu____25187
                                                                    =
                                                                    let uu____25198
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25209
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25198,
                                                                    uu____25209)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25187
                                                                     in
                                                                    (uu____25186,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25179
                                                                     in
                                                                    [uu____25178]
                                                                     in
                                                                    uu____25142
                                                                    ::
                                                                    uu____25175
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25139
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25136
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25133
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25130
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25127
                                                             in
                                                          FStar_List.append
                                                            uu____25100
                                                            uu____25124
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25097
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25094
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25091
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
           (fun uu____25255  ->
              fun se  ->
                match uu____25255 with
                | (g,env1) ->
                    let uu____25275 = encode_sigelt env1 se  in
                    (match uu____25275 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25332 =
        match uu____25332 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25364 ->
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
                 ((let uu____25370 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____25370
                   then
                     let uu____25371 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____25372 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____25373 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25371 uu____25372 uu____25373
                   else ());
                  (let uu____25375 = encode_term t1 env1  in
                   match uu____25375 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____25391 =
                         let uu____25398 =
                           let uu____25399 =
                             let uu____25400 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____25400
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____25399  in
                         new_term_constant_from_string env1 x uu____25398  in
                       (match uu____25391 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____25416 = FStar_Options.log_queries ()
                                 in
                              if uu____25416
                              then
                                let uu____25419 =
                                  let uu____25420 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____25421 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____25422 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25420 uu____25421 uu____25422
                                   in
                                FStar_Pervasives_Native.Some uu____25419
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25438,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____25452 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____25452 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25475,se,uu____25477) ->
                 let uu____25482 = encode_sigelt env1 se  in
                 (match uu____25482 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25499,se) ->
                 let uu____25505 = encode_sigelt env1 se  in
                 (match uu____25505 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____25522 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____25522 with | (uu____25545,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____25557 'Auu____25558 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____25558,'Auu____25557)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25626  ->
              match uu____25626 with
              | (l,uu____25638,uu____25639) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____25685  ->
              match uu____25685 with
              | (l,uu____25699,uu____25700) ->
                  let uu____25709 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____25710 =
                    let uu____25713 =
                      let uu____25714 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____25714  in
                    [uu____25713]  in
                  uu____25709 :: uu____25710))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____25739 =
      let uu____25742 =
        let uu____25743 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____25746 =
          let uu____25747 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____25747 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____25743;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____25746
        }  in
      [uu____25742]  in
    FStar_ST.op_Colon_Equals last_env uu____25739
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____25777 = FStar_ST.op_Bang last_env  in
      match uu____25777 with
      | [] -> failwith "No env; call init first!"
      | e::uu____25804 ->
          let uu___131_25807 = e  in
          let uu____25808 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___131_25807.bindings);
            depth = (uu___131_25807.depth);
            tcenv;
            warn = (uu___131_25807.warn);
            cache = (uu___131_25807.cache);
            nolabels = (uu___131_25807.nolabels);
            use_zfuel_name = (uu___131_25807.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_25807.encode_non_total_function_typ);
            current_module_name = uu____25808
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____25812 = FStar_ST.op_Bang last_env  in
    match uu____25812 with
    | [] -> failwith "Empty env stack"
    | uu____25838::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____25867  ->
    let uu____25868 = FStar_ST.op_Bang last_env  in
    match uu____25868 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___132_25902 = hd1  in
          {
            bindings = (uu___132_25902.bindings);
            depth = (uu___132_25902.depth);
            tcenv = (uu___132_25902.tcenv);
            warn = (uu___132_25902.warn);
            cache = refs;
            nolabels = (uu___132_25902.nolabels);
            use_zfuel_name = (uu___132_25902.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_25902.encode_non_total_function_typ);
            current_module_name = (uu___132_25902.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____25928  ->
    let uu____25929 = FStar_ST.op_Bang last_env  in
    match uu____25929 with
    | [] -> failwith "Popping an empty stack"
    | uu____25955::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
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
        | (uu____26019::uu____26020,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___133_26028 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___133_26028.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___133_26028.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___133_26028.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26029 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26044 =
        let uu____26047 =
          let uu____26048 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26048  in
        let uu____26049 = open_fact_db_tags env  in uu____26047 ::
          uu____26049
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26044
  
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
      let uu____26071 = encode_sigelt env se  in
      match uu____26071 with
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
        let uu____26107 = FStar_Options.log_queries ()  in
        if uu____26107
        then
          let uu____26110 =
            let uu____26111 =
              let uu____26112 =
                let uu____26113 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26113 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26112  in
            FStar_SMTEncoding_Term.Caption uu____26111  in
          uu____26110 :: decls
        else decls  in
      (let uu____26124 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26124
       then
         let uu____26125 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26125
       else ());
      (let env =
         let uu____26128 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26128 tcenv  in
       let uu____26129 = encode_top_level_facts env se  in
       match uu____26129 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26143 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26143)))
  
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
      (let uu____26155 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26155
       then
         let uu____26156 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26156
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26191  ->
                 fun se  ->
                   match uu____26191 with
                   | (g,env2) ->
                       let uu____26211 = encode_top_level_facts env2 se  in
                       (match uu____26211 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26234 =
         encode_signature
           (let uu___134_26243 = env  in
            {
              bindings = (uu___134_26243.bindings);
              depth = (uu___134_26243.depth);
              tcenv = (uu___134_26243.tcenv);
              warn = false;
              cache = (uu___134_26243.cache);
              nolabels = (uu___134_26243.nolabels);
              use_zfuel_name = (uu___134_26243.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_26243.encode_non_total_function_typ);
              current_module_name = (uu___134_26243.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26234 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26260 = FStar_Options.log_queries ()  in
             if uu____26260
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___135_26268 = env1  in
               {
                 bindings = (uu___135_26268.bindings);
                 depth = (uu___135_26268.depth);
                 tcenv = (uu___135_26268.tcenv);
                 warn = true;
                 cache = (uu___135_26268.cache);
                 nolabels = (uu___135_26268.nolabels);
                 use_zfuel_name = (uu___135_26268.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___135_26268.encode_non_total_function_typ);
                 current_module_name = (uu___135_26268.current_module_name)
               });
            (let uu____26270 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____26270
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
        (let uu____26322 =
           let uu____26323 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____26323.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26322);
        (let env =
           let uu____26325 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____26325 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____26337 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26372 = aux rest  in
                 (match uu____26372 with
                  | (out,rest1) ->
                      let t =
                        let uu____26402 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____26402 with
                        | FStar_Pervasives_Native.Some uu____26407 ->
                            let uu____26408 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____26408
                              x.FStar_Syntax_Syntax.sort
                        | uu____26409 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____26413 =
                        let uu____26416 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___136_26419 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_26419.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_26419.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____26416 :: out  in
                      (uu____26413, rest1))
             | uu____26424 -> ([], bindings1)  in
           let uu____26431 = aux bindings  in
           match uu____26431 with
           | (closing,bindings1) ->
               let uu____26456 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____26456, bindings1)
            in
         match uu____26337 with
         | (q1,bindings1) ->
             let uu____26479 =
               let uu____26484 =
                 FStar_List.filter
                   (fun uu___101_26489  ->
                      match uu___101_26489 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26490 ->
                          false
                      | uu____26497 -> true) bindings1
                  in
               encode_env_bindings env uu____26484  in
             (match uu____26479 with
              | (env_decls,env1) ->
                  ((let uu____26515 =
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
                    if uu____26515
                    then
                      let uu____26516 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26516
                    else ());
                   (let uu____26518 = encode_formula q1 env1  in
                    match uu____26518 with
                    | (phi,qdecls) ->
                        let uu____26539 =
                          let uu____26544 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26544 phi
                           in
                        (match uu____26539 with
                         | (labels,phi1) ->
                             let uu____26561 = encode_labels labels  in
                             (match uu____26561 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____26598 =
                                      let uu____26605 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____26606 =
                                        varops.mk_unique "@query"  in
                                      (uu____26605,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26606)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26598
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
  