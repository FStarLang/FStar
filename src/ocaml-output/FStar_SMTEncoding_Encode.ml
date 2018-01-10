open Prims
let add_fuel:
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives () in
      if uu____19 then tl1 else x :: tl1
let withenv:
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____30 ->
      ('Auu____29,'Auu____28) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____28,'Auu____30) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c)
let vargs:
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___77_107  ->
         match uu___77_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___100_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___100_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___100_143.FStar_Syntax_Syntax.sort)
        } in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____145
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____159 in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____160 with
        | (uu____165,t) ->
            let uu____167 =
              let uu____168 = FStar_Syntax_Subst.compress t in
              uu____168.FStar_Syntax_Syntax.n in
            (match uu____167 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____189 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____189 with
                  | (binders,uu____195) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____217
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____224 =
        let uu____229 = mk_term_projector_name lid a in
        (uu____229,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____224
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____236 =
        let uu____241 = mk_term_projector_name_by_pos lid i in
        (uu____241,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____236
let mk_data_tester:
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
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}[@@deriving show]
let __proj__Mkvarops_t__item__push: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
let __proj__Mkvarops_t__item__pop: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
let __proj__Mkvarops_t__item__new_var:
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
let __proj__Mkvarops_t__item__new_fvar:
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
let __proj__Mkvarops_t__item__fresh: varops_t -> Prims.string -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
let __proj__Mkvarops_t__item__string_const:
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
let __proj__Mkvarops_t__item__next_id: varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
let __proj__Mkvarops_t__item__mk_unique:
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____610 =
    let uu____611 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____614 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____611, uu____614) in
  let scopes =
    let uu____634 = let uu____645 = new_scope () in [uu____645] in
    FStar_Util.mk_ref uu____634 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____686 =
        let uu____689 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____689
          (fun uu____801  ->
             match uu____801 with
             | (names1,uu____813) -> FStar_Util.smap_try_find names1 y1) in
      match uu____686 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____822 ->
          (FStar_Util.incr ctr;
           (let uu____857 =
              let uu____858 =
                let uu____859 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____859 in
              Prims.strcat "__" uu____858 in
            Prims.strcat y1 uu____857)) in
    let top_scope =
      let uu____933 =
        let uu____942 = FStar_ST.op_Bang scopes in FStar_List.hd uu____942 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____933 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1080 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1189 =
      let uu____1190 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1190 in
    FStar_Util.format2 "%s_%s" pfx uu____1189 in
  let string_const s =
    let uu____1195 =
      let uu____1198 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1198
        (fun uu____1310  ->
           match uu____1310 with
           | (uu____1321,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1195 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 () in
        let f =
          let uu____1334 = FStar_SMTEncoding_Util.mk_String_const id1 in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1334 in
        let top_scope =
          let uu____1338 =
            let uu____1347 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1347 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1338 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1474 =
    let uu____1475 =
      let uu____1486 = new_scope () in
      let uu____1495 = FStar_ST.op_Bang scopes in uu____1486 :: uu____1495 in
    FStar_ST.op_Colon_Equals scopes uu____1475 in
  let pop1 uu____1697 =
    let uu____1698 =
      let uu____1709 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1709 in
    FStar_ST.op_Colon_Equals scopes uu____1698 in
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
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___101_1911 = x in
    let uu____1912 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1912;
      FStar_Syntax_Syntax.index = (uu___101_1911.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___101_1911.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4[@@deriving show]
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1945 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1981 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____2028 'Auu____2029 .
    'Auu____2029 ->
      ('Auu____2029,'Auu____2028 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkcache_entry__item__cache_symbol_name:
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts:
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
let __proj__Mkcache_entry__item__cache_symbol_decls:
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
let __proj__Mkcache_entry__item__cache_symbol_assumption_names:
  cache_entry -> Prims.string Prims.list =
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
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}[@@deriving show]
let __proj__Mkenv_t__item__bindings: env_t -> binding Prims.list =
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
let __proj__Mkenv_t__item__depth: env_t -> Prims.int =
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
let __proj__Mkenv_t__item__tcenv: env_t -> FStar_TypeChecker_Env.env =
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
let __proj__Mkenv_t__item__warn: env_t -> Prims.bool =
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
let __proj__Mkenv_t__item__cache: env_t -> cache_entry FStar_Util.smap =
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
let __proj__Mkenv_t__item__nolabels: env_t -> Prims.bool =
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
let __proj__Mkenv_t__item__use_zfuel_name: env_t -> Prims.bool =
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
let __proj__Mkenv_t__item__encode_non_total_function_typ: env_t -> Prims.bool
  =
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
let __proj__Mkenv_t__item__current_module_name: env_t -> Prims.string =
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
let mk_cache_entry:
  'Auu____2325 .
    'Auu____2325 ->
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
                 (fun uu___78_2359  ->
                    match uu___78_2359 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2363 -> [])) in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_assumption_names = names1
          }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____2372 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___79_2382  ->
              match uu___79_2382 with
              | Binding_var (x,uu____2384) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2386,uu____2387,uu____2388) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2372 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2402 .
    env_t ->
      (binding -> 'Auu____2402 FStar_Pervasives_Native.option) ->
        'Auu____2402 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2430 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2430
      then
        let uu____2433 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2433
      else FStar_Pervasives_Native.None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____2446 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2446)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___102_2462 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___102_2462.tcenv);
           warn = (uu___102_2462.warn);
           cache = (uu___102_2462.cache);
           nolabels = (uu___102_2462.nolabels);
           use_zfuel_name = (uu___102_2462.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___102_2462.encode_non_total_function_typ);
           current_module_name = (uu___102_2462.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___103_2480 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___103_2480.depth);
           tcenv = (uu___103_2480.tcenv);
           warn = (uu___103_2480.warn);
           cache = (uu___103_2480.cache);
           nolabels = (uu___103_2480.nolabels);
           use_zfuel_name = (uu___103_2480.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___103_2480.encode_non_total_function_typ);
           current_module_name = (uu___103_2480.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___104_2501 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___104_2501.depth);
             tcenv = (uu___104_2501.tcenv);
             warn = (uu___104_2501.warn);
             cache = (uu___104_2501.cache);
             nolabels = (uu___104_2501.nolabels);
             use_zfuel_name = (uu___104_2501.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___104_2501.encode_non_total_function_typ);
             current_module_name = (uu___104_2501.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___105_2511 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___105_2511.depth);
          tcenv = (uu___105_2511.tcenv);
          warn = (uu___105_2511.warn);
          cache = (uu___105_2511.cache);
          nolabels = (uu___105_2511.nolabels);
          use_zfuel_name = (uu___105_2511.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___105_2511.encode_non_total_function_typ);
          current_module_name = (uu___105_2511.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___80_2535  ->
             match uu___80_2535 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2548 -> FStar_Pervasives_Native.None) in
      let uu____2553 = aux a in
      match uu____2553 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2565 = aux a2 in
          (match uu____2565 with
           | FStar_Pervasives_Native.None  ->
               let uu____2576 =
                 let uu____2577 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2578 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2577 uu____2578 in
               failwith uu____2576
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____2605 =
        let uu___106_2606 = env in
        let uu____2607 =
          let uu____2610 =
            let uu____2611 =
              let uu____2624 =
                let uu____2627 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2627 in
              (x, fname, uu____2624, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2611 in
          uu____2610 :: (env.bindings) in
        {
          bindings = uu____2607;
          depth = (uu___106_2606.depth);
          tcenv = (uu___106_2606.tcenv);
          warn = (uu___106_2606.warn);
          cache = (uu___106_2606.cache);
          nolabels = (uu___106_2606.nolabels);
          use_zfuel_name = (uu___106_2606.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___106_2606.encode_non_total_function_typ);
          current_module_name = (uu___106_2606.current_module_name)
        } in
      (fname, ftok, uu____2605)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___81_2669  ->
           match uu___81_2669 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2708 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2725 =
        lookup_binding env
          (fun uu___82_2733  ->
             match uu___82_2733 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2748 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2725 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____2767 = try_lookup_lid env a in
      match uu____2767 with
      | FStar_Pervasives_Native.None  ->
          let uu____2800 =
            let uu____2801 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2801 in
          failwith uu____2800
      | FStar_Pervasives_Native.Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___107_2849 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___107_2849.depth);
            tcenv = (uu___107_2849.tcenv);
            warn = (uu___107_2849.warn);
            cache = (uu___107_2849.cache);
            nolabels = (uu___107_2849.nolabels);
            use_zfuel_name = (uu___107_2849.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___107_2849.encode_non_total_function_typ);
            current_module_name = (uu___107_2849.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2863 = lookup_lid env x in
        match uu____2863 with
        | (t1,t2,uu____2876) ->
            let t3 =
              let uu____2886 =
                let uu____2893 =
                  let uu____2896 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2896] in
                (f, uu____2893) in
              FStar_SMTEncoding_Util.mkApp uu____2886 in
            let uu___108_2901 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___108_2901.depth);
              tcenv = (uu___108_2901.tcenv);
              warn = (uu___108_2901.warn);
              cache = (uu___108_2901.cache);
              nolabels = (uu___108_2901.nolabels);
              use_zfuel_name = (uu___108_2901.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___108_2901.encode_non_total_function_typ);
              current_module_name = (uu___108_2901.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2914 = try_lookup_lid env l in
      match uu____2914 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2963 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2971,fuel::[]) ->
                         let uu____2975 =
                           let uu____2976 =
                             let uu____2977 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2977
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2976 "fuel" in
                         if uu____2975
                         then
                           let uu____2980 =
                             let uu____2981 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2981
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2980
                         else FStar_Pervasives_Native.Some t
                     | uu____2985 -> FStar_Pervasives_Native.Some t)
                | uu____2986 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2999 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2999 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3003 =
            let uu____3004 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3004 in
          failwith uu____3003
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____3015 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3015 with | (x,uu____3027,uu____3028) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3053 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3053 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3089;
                 FStar_SMTEncoding_Term.rng = uu____3090;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3105 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3129 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___83_3145  ->
           match uu___83_3145 with
           | Binding_fvar (uu____3148,nm',tok,uu____3151) when nm = nm' ->
               tok
           | uu____3160 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3164 .
    'Auu____3164 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3182  ->
      match uu____3182 with
      | (pats,vars,body) ->
          let fallback uu____3207 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3212 = FStar_Options.unthrottle_inductives () in
          if uu____3212
          then fallback ()
          else
            (let uu____3214 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3214 with
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
                           | uu____3245 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3266 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3266
                         | uu____3269 ->
                             let uu____3270 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3270 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3275 -> body in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3316 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3329 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3336 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3337 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3354 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3371 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3373 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3373 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3391;
             FStar_Syntax_Syntax.vars = uu____3392;_},uu____3393)
          ->
          let uu____3414 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3414 FStar_Option.isNone
      | uu____3431 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3438 =
        let uu____3439 = FStar_Syntax_Util.un_uinst t in
        uu____3439.FStar_Syntax_Syntax.n in
      match uu____3438 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3442,uu____3443,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___84_3464  ->
                  match uu___84_3464 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3465 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3467 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3467 FStar_Option.isSome
      | uu____3484 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3491 = head_normal env t in
      if uu____3491
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
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____3502 =
      let uu____3503 = FStar_Syntax_Syntax.null_binder t in [uu____3503] in
    let uu____3504 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3502 uu____3504 FStar_Pervasives_Native.None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3542 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3542
                | s ->
                    let uu____3547 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3547) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___85_3562  ->
    match uu___85_3562 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3563 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
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
                       FStar_SMTEncoding_Term.freevars = uu____3599;
                       FStar_SMTEncoding_Term.rng = uu____3600;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3623) ->
              let uu____3632 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3643 -> false) args (FStar_List.rev xs)) in
              if uu____3632
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3647,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3651 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3655 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3655)) in
              if uu____3651
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3659 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list;}[@@deriving show]
let __proj__Mkpattern__item__pat_vars:
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let __proj__Mkpattern__item__pat_term:
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
let __proj__Mkpattern__item__guard:
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
let __proj__Mkpattern__item__projections:
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3881 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3885 -> false
let as_function_typ:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3904 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3917 ->
            let uu____3924 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3924
        | uu____3925 ->
            if norm1
            then let uu____3926 = whnf env t1 in aux false uu____3926
            else
              (let uu____3928 =
                 let uu____3929 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3930 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3929 uu____3930 in
               failwith uu____3928) in
      aux true t0
let rec curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3962) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3967 ->
        let uu____3968 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3968)
let is_arithmetic_primitive:
  'Auu____3982 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3982 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4002::uu____4003::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4007::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4010 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4031 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4046 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4050 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4050)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4089)::uu____4090::uu____4091::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4142)::uu____4143::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4180 -> false
let rec encode_const:
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4399 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4399, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4402 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4402, [])
      | FStar_Const.Const_char c1 ->
          let uu____4406 =
            let uu____4407 =
              let uu____4414 =
                let uu____4417 =
                  let uu____4418 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4418 in
                [uu____4417] in
              ("FStar.Char.__char_of_int", uu____4414) in
            FStar_SMTEncoding_Util.mkApp uu____4407 in
          (uu____4406, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4434 =
            let uu____4435 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4435 in
          (uu____4434, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4456) ->
          let uu____4457 = varops.string_const s in (uu____4457, [])
      | FStar_Const.Const_range uu____4460 ->
          let uu____4461 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4461, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4467 =
            let uu____4468 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4468 in
          failwith uu____4467
and encode_binders:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4497 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4497
         then
           let uu____4498 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4498
         else ());
        (let uu____4500 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4584  ->
                   fun b  ->
                     match uu____4584 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4663 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4679 = gen_term_var env1 x in
                           match uu____4679 with
                           | (xxsym,xx,env') ->
                               let uu____4703 =
                                 let uu____4708 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4708 env1 xx in
                               (match uu____4703 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4663 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4500 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4867 = encode_term t env in
          match uu____4867 with
          | (t1,decls) ->
              let uu____4878 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4878, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4889 = encode_term t env in
          match uu____4889 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4904 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4904, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4906 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4906, decls))
and encode_arith_term:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4912 = encode_args args_e env in
        match uu____4912 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4931 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4940 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4940 in
            let binary arg_tms1 =
              let uu____4953 =
                let uu____4954 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4954 in
              let uu____4955 =
                let uu____4956 =
                  let uu____4957 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4957 in
                FStar_SMTEncoding_Term.unboxInt uu____4956 in
              (uu____4953, uu____4955) in
            let mk_default uu____4963 =
              let uu____4964 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4964 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5015 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5015
              then
                let uu____5016 = let uu____5017 = mk_args ts in op uu____5017 in
                FStar_All.pipe_right uu____5016 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5046 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5046
              then
                let uu____5047 = binary ts in
                match uu____5047 with
                | (t1,t2) ->
                    let uu____5054 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5054
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5058 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5058
                 then
                   let uu____5059 = op (binary ts) in
                   FStar_All.pipe_right uu____5059
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____5190 =
              let uu____5199 =
                FStar_List.tryFind
                  (fun uu____5221  ->
                     match uu____5221 with
                     | (l,uu____5231) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5199 FStar_Util.must in
            (match uu____5190 with
             | (uu____5270,op) ->
                 let uu____5280 = op arg_tms in (uu____5280, decls))
and encode_BitVector_term:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5288 = FStar_List.hd args_e in
        match uu____5288 with
        | (tm_sz,uu____5296) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5306 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5306 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5314 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5314);
                   t_decls) in
            let uu____5315 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5335::(sz_arg,uu____5337)::uu____5338::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5387 =
                    let uu____5390 = FStar_List.tail args_e in
                    FStar_List.tail uu____5390 in
                  let uu____5393 =
                    let uu____5396 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5396 in
                  (uu____5387, uu____5393)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5402::(sz_arg,uu____5404)::uu____5405::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5454 =
                    let uu____5455 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5455 in
                  failwith uu____5454
              | uu____5464 ->
                  let uu____5471 = FStar_List.tail args_e in
                  (uu____5471, FStar_Pervasives_Native.None) in
            (match uu____5315 with
             | (arg_tms,ext_sz) ->
                 let uu____5494 = encode_args arg_tms env in
                 (match uu____5494 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5515 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5524 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5524 in
                      let unary_arith arg_tms2 =
                        let uu____5533 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5533 in
                      let binary arg_tms2 =
                        let uu____5546 =
                          let uu____5547 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5547 in
                        let uu____5548 =
                          let uu____5549 =
                            let uu____5550 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5550 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5549 in
                        (uu____5546, uu____5548) in
                      let binary_arith arg_tms2 =
                        let uu____5565 =
                          let uu____5566 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5566 in
                        let uu____5567 =
                          let uu____5568 =
                            let uu____5569 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5569 in
                          FStar_SMTEncoding_Term.unboxInt uu____5568 in
                        (uu____5565, uu____5567) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5618 =
                          let uu____5619 = mk_args ts in op uu____5619 in
                        FStar_All.pipe_right uu____5618 resBox in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu____5727 =
                          let uu____5730 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5730 in
                        let uu____5732 =
                          let uu____5735 =
                            let uu____5736 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5736 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5735 in
                        mk_bv uu____5727 unary uu____5732 arg_tms2 in
                      let to_int1 =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
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
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____5935 =
                        let uu____5944 =
                          FStar_List.tryFind
                            (fun uu____5966  ->
                               match uu____5966 with
                               | (l,uu____5976) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5944 FStar_Util.must in
                      (match uu____5935 with
                       | (uu____6017,op) ->
                           let uu____6027 = op arg_tms1 in
                           (uu____6027, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6038 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6038
       then
         let uu____6039 = FStar_Syntax_Print.tag_of_term t in
         let uu____6040 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6041 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6039 uu____6040
           uu____6041
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6047 ->
           let uu____6072 =
             let uu____6073 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6074 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6075 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6076 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6073
               uu____6074 uu____6075 uu____6076 in
           failwith uu____6072
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6081 =
             let uu____6082 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6083 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6084 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6085 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6082
               uu____6083 uu____6084 uu____6085 in
           failwith uu____6081
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6091 =
             let uu____6092 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6092 in
           failwith uu____6091
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6099) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6140;
              FStar_Syntax_Syntax.vars = uu____6141;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6158 = varops.fresh "t" in
             (uu____6158, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6161 =
               let uu____6172 =
                 let uu____6175 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6175 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6172) in
             FStar_SMTEncoding_Term.DeclFun uu____6161 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6183) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6193 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6193, [])
       | FStar_Syntax_Syntax.Tm_type uu____6196 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6200) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6225 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6225 with
            | (binders1,res) ->
                let uu____6236 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6236
                then
                  let uu____6241 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6241 with
                   | (vars,guards,env',decls,uu____6266) ->
                       let fsym =
                         let uu____6284 = varops.fresh "f" in
                         (uu____6284, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6287 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___109_6296 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___109_6296.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___109_6296.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___109_6296.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___109_6296.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___109_6296.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___109_6296.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___109_6296.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___109_6296.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___109_6296.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___109_6296.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___109_6296.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___109_6296.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___109_6296.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___109_6296.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___109_6296.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___109_6296.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___109_6296.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___109_6296.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___109_6296.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___109_6296.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___109_6296.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___109_6296.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___109_6296.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___109_6296.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___109_6296.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___109_6296.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___109_6296.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___109_6296.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___109_6296.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___109_6296.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___109_6296.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___109_6296.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___109_6296.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6287 with
                        | (pre_opt,res_t) ->
                            let uu____6307 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6307 with
                             | (res_pred,decls') ->
                                 let uu____6318 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6331 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6331, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6335 =
                                         encode_formula pre env' in
                                       (match uu____6335 with
                                        | (guard,decls0) ->
                                            let uu____6348 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6348, decls0)) in
                                 (match uu____6318 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6360 =
                                          let uu____6371 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6371) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6360 in
                                      let cvars =
                                        let uu____6389 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6389
                                          (FStar_List.filter
                                             (fun uu____6403  ->
                                                match uu____6403 with
                                                | (x,uu____6409) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6428 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6428 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6436 =
                                             let uu____6437 =
                                               let uu____6444 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6444) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6437 in
                                           (uu____6436,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6464 =
                                               let uu____6465 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6465 in
                                             varops.mk_unique uu____6464 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6476 =
                                               FStar_Options.log_queries () in
                                             if uu____6476
                                             then
                                               let uu____6479 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6479
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6487 =
                                               let uu____6494 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6494) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6487 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6506 =
                                               let uu____6513 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6513,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6506 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____6534 =
                                               let uu____6541 =
                                                 let uu____6542 =
                                                   let uu____6553 =
                                                     let uu____6554 =
                                                       let uu____6559 =
                                                         let uu____6560 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6560 in
                                                       (f_has_t, uu____6559) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6554 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6553) in
                                                 mkForall_fuel uu____6542 in
                                               (uu____6541,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6534 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6583 =
                                               let uu____6590 =
                                                 let uu____6591 =
                                                   let uu____6602 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6602) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6591 in
                                               (uu____6590,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6583 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6627 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6627);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____6642 =
                       let uu____6649 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6649,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6642 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6661 =
                       let uu____6668 =
                         let uu____6669 =
                           let uu____6680 =
                             let uu____6681 =
                               let uu____6686 =
                                 let uu____6687 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6687 in
                               (f_has_t, uu____6686) in
                             FStar_SMTEncoding_Util.mkImp uu____6681 in
                           ([[f_has_t]], [fsym], uu____6680) in
                         mkForall_fuel uu____6669 in
                       (uu____6668, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6661 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6714 ->
           let uu____6721 =
             let uu____6726 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6726 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6733;
                 FStar_Syntax_Syntax.vars = uu____6734;_} ->
                 let uu____6741 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6741 with
                  | (b,f1) ->
                      let uu____6766 =
                        let uu____6767 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6767 in
                      (uu____6766, f1))
             | uu____6776 -> failwith "impossible" in
           (match uu____6721 with
            | (x,f) ->
                let uu____6787 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6787 with
                 | (base_t,decls) ->
                     let uu____6798 = gen_term_var env x in
                     (match uu____6798 with
                      | (x1,xtm,env') ->
                          let uu____6812 = encode_formula f env' in
                          (match uu____6812 with
                           | (refinement,decls') ->
                               let uu____6823 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6823 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6839 =
                                        let uu____6842 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6849 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6842
                                          uu____6849 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6839 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6882  ->
                                              match uu____6882 with
                                              | (y,uu____6888) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____6921 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6921 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6929 =
                                           let uu____6930 =
                                             let uu____6937 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6937) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6930 in
                                         (uu____6929,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6958 =
                                             let uu____6959 =
                                               let uu____6960 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6960 in
                                             Prims.strcat module_name
                                               uu____6959 in
                                           varops.mk_unique uu____6958 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____6974 =
                                             let uu____6981 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6981) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6974 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____6996 =
                                             let uu____7003 =
                                               let uu____7004 =
                                                 let uu____7015 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7015) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7004 in
                                             (uu____7003,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6996 in
                                         let t_kinding =
                                           let uu____7033 =
                                             let uu____7040 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7040,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7033 in
                                         let t_interp =
                                           let uu____7058 =
                                             let uu____7065 =
                                               let uu____7066 =
                                                 let uu____7077 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7077) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7066 in
                                             let uu____7100 =
                                               let uu____7103 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7103 in
                                             (uu____7065, uu____7100,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7058 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7110 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7110);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7140 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7140 in
           let uu____7141 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7141 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7153 =
                    let uu____7160 =
                      let uu____7161 =
                        let uu____7162 =
                          let uu____7163 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7163 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7162 in
                      varops.mk_unique uu____7161 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7160) in
                  FStar_SMTEncoding_Util.mkAssume uu____7153 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7168 ->
           let uu____7183 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7183 with
            | (head1,args_e) ->
                let uu____7224 =
                  let uu____7237 =
                    let uu____7238 = FStar_Syntax_Subst.compress head1 in
                    uu____7238.FStar_Syntax_Syntax.n in
                  (uu____7237, args_e) in
                (match uu____7224 with
                 | uu____7253 when head_redex env head1 ->
                     let uu____7266 = whnf env t in
                     encode_term uu____7266 env
                 | uu____7267 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7286 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7300;
                       FStar_Syntax_Syntax.vars = uu____7301;_},uu____7302),uu____7303::
                    (v1,uu____7305)::(v2,uu____7307)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7358 = encode_term v1 env in
                     (match uu____7358 with
                      | (v11,decls1) ->
                          let uu____7369 = encode_term v2 env in
                          (match uu____7369 with
                           | (v21,decls2) ->
                               let uu____7380 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7380,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7384::(v1,uu____7386)::(v2,uu____7388)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7435 = encode_term v1 env in
                     (match uu____7435 with
                      | (v11,decls1) ->
                          let uu____7446 = encode_term v2 env in
                          (match uu____7446 with
                           | (v21,decls2) ->
                               let uu____7457 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7457,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7461)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7487)::(rng,uu____7489)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7524) ->
                     let e0 =
                       let uu____7542 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7542 in
                     ((let uu____7550 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7550
                       then
                         let uu____7551 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7551
                       else ());
                      (let e =
                         let uu____7556 =
                           let uu____7557 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7558 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7557
                             uu____7558 in
                         uu____7556 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7567),(arg,uu____7569)::[]) -> encode_term arg env
                 | uu____7594 ->
                     let uu____7607 = encode_args args_e env in
                     (match uu____7607 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7662 = encode_term head1 env in
                            match uu____7662 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7726 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7726 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7804  ->
                                                 fun uu____7805  ->
                                                   match (uu____7804,
                                                           uu____7805)
                                                   with
                                                   | ((bv,uu____7827),
                                                      (a,uu____7829)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7847 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7847
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7852 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7852 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7867 =
                                                   let uu____7874 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7883 =
                                                     let uu____7884 =
                                                       let uu____7885 =
                                                         let uu____7886 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7886 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7885 in
                                                     varops.mk_unique
                                                       uu____7884 in
                                                   (uu____7874,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7883) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7867 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7903 = lookup_free_var_sym env fv in
                            match uu____7903 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____7934;
                                   FStar_Syntax_Syntax.vars = uu____7935;_},uu____7936)
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
                                   FStar_Syntax_Syntax.pos = uu____7947;
                                   FStar_Syntax_Syntax.vars = uu____7948;_},uu____7949)
                                ->
                                let uu____7954 =
                                  let uu____7955 =
                                    let uu____7960 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7960
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7955
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7954
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7990 =
                                  let uu____7991 =
                                    let uu____7996 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7996
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7991
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7990
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8025,(FStar_Util.Inl t1,uu____8027),uu____8028)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8077,(FStar_Util.Inr c,uu____8079),uu____8080)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8129 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8156 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8156 in
                               let uu____8157 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8157 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8173;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8174;_},uu____8175)
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
                                     | uu____8189 ->
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
           let uu____8238 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8238 with
            | (bs1,body1,opening) ->
                let fallback uu____8261 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8268 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8268, [decl]) in
                let is_impure rc =
                  let uu____8275 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8275 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8285 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8285
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8305 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8305
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8309 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8309)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8316 =
                         let uu____8321 =
                           let uu____8322 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8322 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8321) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8316);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8324 =
                       (is_impure rc) &&
                         (let uu____8326 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8326) in
                     if uu____8324
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8333 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8333 with
                        | (vars,guards,envbody,decls,uu____8358) ->
                            let body2 =
                              let uu____8372 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8372
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8374 = encode_term body2 envbody in
                            (match uu____8374 with
                             | (body3,decls') ->
                                 let uu____8385 =
                                   let uu____8394 = codomain_eff rc in
                                   match uu____8394 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8413 = encode_term tfun env in
                                       (match uu____8413 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8385 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8445 =
                                          let uu____8456 =
                                            let uu____8457 =
                                              let uu____8462 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8462, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8457 in
                                          ([], vars, uu____8456) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8445 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8474 =
                                              let uu____8477 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8477
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8474 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8496 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8496 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8504 =
                                             let uu____8505 =
                                               let uu____8512 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8512) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8505 in
                                           (uu____8504,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8523 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8523 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8534 =
                                                    let uu____8535 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8535 = cache_size in
                                                  if uu____8534
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'') in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1 in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____8551 =
                                                      let uu____8552 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8552 in
                                                    varops.mk_unique
                                                      uu____8551 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8559 =
                                                    let uu____8566 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8566) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8559 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1 in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym in
                                                      let uu____8584 =
                                                        let uu____8585 =
                                                          let uu____8592 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8592,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8585 in
                                                      [uu____8584] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8605 =
                                                    let uu____8612 =
                                                      let uu____8613 =
                                                        let uu____8624 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8624) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8613 in
                                                    (uu____8612,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8605 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8641 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8641);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8644,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8645;
                          FStar_Syntax_Syntax.lbunivs = uu____8646;
                          FStar_Syntax_Syntax.lbtyp = uu____8647;
                          FStar_Syntax_Syntax.lbeff = uu____8648;
                          FStar_Syntax_Syntax.lbdef = uu____8649;_}::uu____8650),uu____8651)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8677;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8679;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8700 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
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
                FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____8770 = encode_term e1 env in
              match uu____8770 with
              | (ee1,decls1) ->
                  let uu____8781 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8781 with
                   | (xs,e21) ->
                       let uu____8806 = FStar_List.hd xs in
                       (match uu____8806 with
                        | (x1,uu____8820) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8822 = encode_body e21 env' in
                            (match uu____8822 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
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
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____8854 =
              let uu____8861 =
                let uu____8862 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8862 in
              gen_term_var env uu____8861 in
            match uu____8854 with
            | (scrsym,scr',env1) ->
                let uu____8870 = encode_term e env1 in
                (match uu____8870 with
                 | (scr,decls) ->
                     let uu____8881 =
                       let encode_branch b uu____8906 =
                         match uu____8906 with
                         | (else_case,decls1) ->
                             let uu____8925 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8925 with
                              | (p,w,br) ->
                                  let uu____8951 = encode_pat env1 p in
                                  (match uu____8951 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8988  ->
                                                   match uu____8988 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8995 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9017 =
                                               encode_term w1 env2 in
                                             (match uu____9017 with
                                              | (w2,decls2) ->
                                                  let uu____9030 =
                                                    let uu____9031 =
                                                      let uu____9036 =
                                                        let uu____9037 =
                                                          let uu____9042 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9042) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9037 in
                                                      (guard, uu____9036) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9031 in
                                                  (uu____9030, decls2)) in
                                       (match uu____8995 with
                                        | (guard1,decls2) ->
                                            let uu____9055 =
                                              encode_br br env2 in
                                            (match uu____9055 with
                                             | (br1,decls3) ->
                                                 let uu____9068 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9068,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8881 with
                      | (match_tm,decls1) ->
                          let uu____9087 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9087, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9127 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9127
       then
         let uu____9128 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9128
       else ());
      (let uu____9130 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9130 with
       | (vars,pat_term) ->
           let uu____9147 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9200  ->
                     fun v1  ->
                       match uu____9200 with
                       | (env1,vars1) ->
                           let uu____9252 = gen_term_var env1 v1 in
                           (match uu____9252 with
                            | (xx,uu____9274,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9147 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9353 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9354 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9355 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9363 = encode_const c env1 in
                      (match uu____9363 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9377::uu____9378 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9381 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9404 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9404 with
                        | (uu____9411,uu____9412::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9415 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9448  ->
                                  match uu____9448 with
                                  | (arg,uu____9456) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9462 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9462)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9489) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9520 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9543 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9587  ->
                                  match uu____9587 with
                                  | (arg,uu____9601) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9607 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9607)) in
                      FStar_All.pipe_right uu____9543 FStar_List.flatten in
                let pat_term1 uu____9635 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____9645 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9683  ->
                fun uu____9684  ->
                  match (uu____9683, uu____9684) with
                  | ((tms,decls),(t,uu____9720)) ->
                      let uu____9741 = encode_term t env in
                      (match uu____9741 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9645 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9798 = FStar_Syntax_Util.list_elements e in
        match uu____9798 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9819 =
          let uu____9834 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9834 FStar_Syntax_Util.head_and_args in
        match uu____9819 with
        | (head1,args) ->
            let uu____9873 =
              let uu____9886 =
                let uu____9887 = FStar_Syntax_Util.un_uinst head1 in
                uu____9887.FStar_Syntax_Syntax.n in
              (uu____9886, args) in
            (match uu____9873 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9901,uu____9902)::(e,uu____9904)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9939 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9975 =
            let uu____9990 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9990 FStar_Syntax_Util.head_and_args in
          match uu____9975 with
          | (head1,args) ->
              let uu____10031 =
                let uu____10044 =
                  let uu____10045 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10045.FStar_Syntax_Syntax.n in
                (uu____10044, args) in
              (match uu____10031 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10062)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10089 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10111 = smt_pat_or1 t1 in
            (match uu____10111 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10127 = list_elements1 e in
                 FStar_All.pipe_right uu____10127
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10145 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10145
                           (FStar_List.map one_pat)))
             | uu____10156 ->
                 let uu____10161 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10161])
        | uu____10182 ->
            let uu____10185 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10185] in
      let uu____10206 =
        let uu____10225 =
          let uu____10226 = FStar_Syntax_Subst.compress t in
          uu____10226.FStar_Syntax_Syntax.n in
        match uu____10225 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10265 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10265 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10308;
                        FStar_Syntax_Syntax.effect_name = uu____10309;
                        FStar_Syntax_Syntax.result_typ = uu____10310;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10312)::(post,uu____10314)::(pats,uu____10316)::[];
                        FStar_Syntax_Syntax.flags = uu____10317;_}
                      ->
                      let uu____10358 = lemma_pats pats in
                      (binders1, pre, post, uu____10358)
                  | uu____10375 -> failwith "impos"))
        | uu____10394 -> failwith "Impos" in
      match uu____10206 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___110_10442 = env in
            {
              bindings = (uu___110_10442.bindings);
              depth = (uu___110_10442.depth);
              tcenv = (uu___110_10442.tcenv);
              warn = (uu___110_10442.warn);
              cache = (uu___110_10442.cache);
              nolabels = (uu___110_10442.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___110_10442.encode_non_total_function_typ);
              current_module_name = (uu___110_10442.current_module_name)
            } in
          let uu____10443 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10443 with
           | (vars,guards,env2,decls,uu____10468) ->
               let uu____10481 =
                 let uu____10496 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10550 =
                             let uu____10561 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2)) in
                             FStar_All.pipe_right uu____10561
                               FStar_List.unzip in
                           match uu____10550 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10496 FStar_List.unzip in
               (match uu____10481 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___111_10713 = env2 in
                      {
                        bindings = (uu___111_10713.bindings);
                        depth = (uu___111_10713.depth);
                        tcenv = (uu___111_10713.tcenv);
                        warn = (uu___111_10713.warn);
                        cache = (uu___111_10713.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___111_10713.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___111_10713.encode_non_total_function_typ);
                        current_module_name =
                          (uu___111_10713.current_module_name)
                      } in
                    let uu____10714 =
                      let uu____10719 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10719 env3 in
                    (match uu____10714 with
                     | (pre1,decls'') ->
                         let uu____10726 =
                           let uu____10731 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10731 env3 in
                         (match uu____10726 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10741 =
                                let uu____10742 =
                                  let uu____10753 =
                                    let uu____10754 =
                                      let uu____10759 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10759, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10754 in
                                  (pats, vars, uu____10753) in
                                FStar_SMTEncoding_Util.mkForall uu____10742 in
                              (uu____10741, decls1)))))
and encode_smt_pattern:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let uu____10772 = FStar_Syntax_Util.head_and_args t in
      match uu____10772 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1 in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10831::(x,uu____10833)::(t1,uu____10835)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10882 = encode_term x env in
               (match uu____10882 with
                | (x1,decls) ->
                    let uu____10895 = encode_term t1 env in
                    (match uu____10895 with
                     | (t2,decls') ->
                         let uu____10908 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                         (uu____10908, (FStar_List.append decls decls'))))
           | uu____10911 -> encode_term t env)
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10934 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10934
        then
          let uu____10935 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10936 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10935 uu____10936
        else () in
      let enc f r l =
        let uu____10969 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10997 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10997 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10969 with
        | (decls,args) ->
            let uu____11026 =
              let uu___112_11027 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___112_11027.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___112_11027.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11026, decls) in
      let const_op f r uu____11058 =
        let uu____11071 = f r in (uu____11071, []) in
      let un_op f l =
        let uu____11090 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11090 in
      let bin_op f uu___86_11106 =
        match uu___86_11106 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11117 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11151 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11174  ->
                 match uu____11174 with
                 | (t,uu____11188) ->
                     let uu____11189 = encode_formula t env in
                     (match uu____11189 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11151 with
        | (decls,phis) ->
            let uu____11218 =
              let uu___113_11219 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___113_11219.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___113_11219.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11218, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11280  ->
               match uu____11280 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11299) -> false
                    | uu____11300 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11315 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11315
        else
          (let uu____11329 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11329 r rf) in
      let mk_imp1 r uu___87_11354 =
        match uu___87_11354 with
        | (lhs,uu____11360)::(rhs,uu____11362)::[] ->
            let uu____11389 = encode_formula rhs env in
            (match uu____11389 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11404) ->
                      (l1, decls1)
                  | uu____11409 ->
                      let uu____11410 = encode_formula lhs env in
                      (match uu____11410 with
                       | (l2,decls2) ->
                           let uu____11421 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11421, (FStar_List.append decls1 decls2)))))
        | uu____11424 -> failwith "impossible" in
      let mk_ite r uu___88_11445 =
        match uu___88_11445 with
        | (guard,uu____11451)::(_then,uu____11453)::(_else,uu____11455)::[]
            ->
            let uu____11492 = encode_formula guard env in
            (match uu____11492 with
             | (g,decls1) ->
                 let uu____11503 = encode_formula _then env in
                 (match uu____11503 with
                  | (t,decls2) ->
                      let uu____11514 = encode_formula _else env in
                      (match uu____11514 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11528 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11553 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11553 in
      let connectives =
        let uu____11571 =
          let uu____11584 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11584) in
        let uu____11601 =
          let uu____11616 =
            let uu____11629 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11629) in
          let uu____11646 =
            let uu____11661 =
              let uu____11676 =
                let uu____11689 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11689) in
              let uu____11706 =
                let uu____11721 =
                  let uu____11736 =
                    let uu____11749 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11749) in
                  [uu____11736;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11721 in
              uu____11676 :: uu____11706 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11661 in
          uu____11616 :: uu____11646 in
        uu____11571 :: uu____11601 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12070 = encode_formula phi' env in
            (match uu____12070 with
             | (phi2,decls) ->
                 let uu____12081 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12081, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12082 ->
            let uu____12089 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12089 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12128 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12128 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12140;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12142;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12163 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12163 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12210::(x,uu____12212)::(t,uu____12214)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12261 = encode_term x env in
                 (match uu____12261 with
                  | (x1,decls) ->
                      let uu____12272 = encode_term t env in
                      (match uu____12272 with
                       | (t1,decls') ->
                           let uu____12283 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12283, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12288)::(msg,uu____12290)::(phi2,uu____12292)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12337 =
                   let uu____12342 =
                     let uu____12343 = FStar_Syntax_Subst.compress r in
                     uu____12343.FStar_Syntax_Syntax.n in
                   let uu____12346 =
                     let uu____12347 = FStar_Syntax_Subst.compress msg in
                     uu____12347.FStar_Syntax_Syntax.n in
                   (uu____12342, uu____12346) in
                 (match uu____12337 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12356))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12362 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12369)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12394 when head_redex env head2 ->
                 let uu____12407 = whnf env phi1 in
                 encode_formula uu____12407 env
             | uu____12408 ->
                 let uu____12421 = encode_term phi1 env in
                 (match uu____12421 with
                  | (tt,decls) ->
                      let uu____12432 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___114_12435 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___114_12435.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___114_12435.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12432, decls)))
        | uu____12436 ->
            let uu____12437 = encode_term phi1 env in
            (match uu____12437 with
             | (tt,decls) ->
                 let uu____12448 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___115_12451 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___115_12451.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___115_12451.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12448, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12487 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12487 with
        | (vars,guards,env2,decls,uu____12526) ->
            let uu____12539 =
              let uu____12552 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12604 =
                          let uu____12615 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12655  ->
                                    match uu____12655 with
                                    | (t,uu____12669) ->
                                        encode_smt_pattern t
                                          (let uu___116_12675 = env2 in
                                           {
                                             bindings =
                                               (uu___116_12675.bindings);
                                             depth = (uu___116_12675.depth);
                                             tcenv = (uu___116_12675.tcenv);
                                             warn = (uu___116_12675.warn);
                                             cache = (uu___116_12675.cache);
                                             nolabels =
                                               (uu___116_12675.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___116_12675.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___116_12675.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12615 FStar_List.unzip in
                        match uu____12604 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12552 FStar_List.unzip in
            (match uu____12539 with
             | (pats,decls') ->
                 let uu____12784 = encode_formula body env2 in
                 (match uu____12784 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12816;
                             FStar_SMTEncoding_Term.rng = uu____12817;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12832 -> guards in
                      let uu____12837 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12837, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12897  ->
                   match uu____12897 with
                   | (x,uu____12903) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12911 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12923 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12923) uu____12911 tl1 in
             let uu____12926 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12953  ->
                       match uu____12953 with
                       | (b,uu____12959) ->
                           let uu____12960 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12960)) in
             (match uu____12926 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12966) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12980 =
                    let uu____12985 =
                      let uu____12986 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12986 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12985) in
                  FStar_Errors.log_issue pos uu____12980) in
       let uu____12987 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12987 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12996 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13054  ->
                     match uu____13054 with
                     | (l,uu____13068) -> FStar_Ident.lid_equals op l)) in
           (match uu____12996 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13101,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13141 = encode_q_body env vars pats body in
             match uu____13141 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13186 =
                     let uu____13197 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13197) in
                   FStar_SMTEncoding_Term.mkForall uu____13186
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13216 = encode_q_body env vars pats body in
             match uu____13216 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13260 =
                   let uu____13261 =
                     let uu____13272 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13272) in
                   FStar_SMTEncoding_Term.mkExists uu____13261
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13260, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}[@@deriving show]
let __proj__Mkprims_t__item__mk:
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
let __proj__Mkprims_t__item__is: prims_t -> FStar_Ident.lident -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
let prims: prims_t =
  let uu____13365 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13365 with
  | (asym,a) ->
      let uu____13372 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13372 with
       | (xsym,x) ->
           let uu____13379 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13379 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13423 =
                      let uu____13434 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13434, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13423 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13460 =
                      let uu____13467 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13467) in
                    FStar_SMTEncoding_Util.mkApp uu____13460 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13480 =
                    let uu____13483 =
                      let uu____13486 =
                        let uu____13489 =
                          let uu____13490 =
                            let uu____13497 =
                              let uu____13498 =
                                let uu____13509 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13509) in
                              FStar_SMTEncoding_Util.mkForall uu____13498 in
                            (uu____13497, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13490 in
                        let uu____13526 =
                          let uu____13529 =
                            let uu____13530 =
                              let uu____13537 =
                                let uu____13538 =
                                  let uu____13549 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13549) in
                                FStar_SMTEncoding_Util.mkForall uu____13538 in
                              (uu____13537,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13530 in
                          [uu____13529] in
                        uu____13489 :: uu____13526 in
                      xtok_decl :: uu____13486 in
                    xname_decl :: uu____13483 in
                  (xtok1, uu____13480) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13640 =
                    let uu____13653 =
                      let uu____13662 =
                        let uu____13663 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13663 in
                      quant axy uu____13662 in
                    (FStar_Parser_Const.op_Eq, uu____13653) in
                  let uu____13672 =
                    let uu____13687 =
                      let uu____13700 =
                        let uu____13709 =
                          let uu____13710 =
                            let uu____13711 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13711 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13710 in
                        quant axy uu____13709 in
                      (FStar_Parser_Const.op_notEq, uu____13700) in
                    let uu____13720 =
                      let uu____13735 =
                        let uu____13748 =
                          let uu____13757 =
                            let uu____13758 =
                              let uu____13759 =
                                let uu____13764 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13765 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13764, uu____13765) in
                              FStar_SMTEncoding_Util.mkLT uu____13759 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13758 in
                          quant xy uu____13757 in
                        (FStar_Parser_Const.op_LT, uu____13748) in
                      let uu____13774 =
                        let uu____13789 =
                          let uu____13802 =
                            let uu____13811 =
                              let uu____13812 =
                                let uu____13813 =
                                  let uu____13818 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13819 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13818, uu____13819) in
                                FStar_SMTEncoding_Util.mkLTE uu____13813 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13812 in
                            quant xy uu____13811 in
                          (FStar_Parser_Const.op_LTE, uu____13802) in
                        let uu____13828 =
                          let uu____13843 =
                            let uu____13856 =
                              let uu____13865 =
                                let uu____13866 =
                                  let uu____13867 =
                                    let uu____13872 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13873 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13872, uu____13873) in
                                  FStar_SMTEncoding_Util.mkGT uu____13867 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13866 in
                              quant xy uu____13865 in
                            (FStar_Parser_Const.op_GT, uu____13856) in
                          let uu____13882 =
                            let uu____13897 =
                              let uu____13910 =
                                let uu____13919 =
                                  let uu____13920 =
                                    let uu____13921 =
                                      let uu____13926 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13927 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13926, uu____13927) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13921 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13920 in
                                quant xy uu____13919 in
                              (FStar_Parser_Const.op_GTE, uu____13910) in
                            let uu____13936 =
                              let uu____13951 =
                                let uu____13964 =
                                  let uu____13973 =
                                    let uu____13974 =
                                      let uu____13975 =
                                        let uu____13980 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13981 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13980, uu____13981) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13975 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13974 in
                                  quant xy uu____13973 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13964) in
                              let uu____13990 =
                                let uu____14005 =
                                  let uu____14018 =
                                    let uu____14027 =
                                      let uu____14028 =
                                        let uu____14029 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14029 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14028 in
                                    quant qx uu____14027 in
                                  (FStar_Parser_Const.op_Minus, uu____14018) in
                                let uu____14038 =
                                  let uu____14053 =
                                    let uu____14066 =
                                      let uu____14075 =
                                        let uu____14076 =
                                          let uu____14077 =
                                            let uu____14082 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14083 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14082, uu____14083) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14077 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14076 in
                                      quant xy uu____14075 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14066) in
                                  let uu____14092 =
                                    let uu____14107 =
                                      let uu____14120 =
                                        let uu____14129 =
                                          let uu____14130 =
                                            let uu____14131 =
                                              let uu____14136 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14137 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14136, uu____14137) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14131 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14130 in
                                        quant xy uu____14129 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14120) in
                                    let uu____14146 =
                                      let uu____14161 =
                                        let uu____14174 =
                                          let uu____14183 =
                                            let uu____14184 =
                                              let uu____14185 =
                                                let uu____14190 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14191 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14190, uu____14191) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14185 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14184 in
                                          quant xy uu____14183 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14174) in
                                      let uu____14200 =
                                        let uu____14215 =
                                          let uu____14228 =
                                            let uu____14237 =
                                              let uu____14238 =
                                                let uu____14239 =
                                                  let uu____14244 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14245 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14244, uu____14245) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14239 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14238 in
                                            quant xy uu____14237 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14228) in
                                        let uu____14254 =
                                          let uu____14269 =
                                            let uu____14282 =
                                              let uu____14291 =
                                                let uu____14292 =
                                                  let uu____14293 =
                                                    let uu____14298 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14299 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14298,
                                                      uu____14299) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14293 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14292 in
                                              quant xy uu____14291 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14282) in
                                          let uu____14308 =
                                            let uu____14323 =
                                              let uu____14336 =
                                                let uu____14345 =
                                                  let uu____14346 =
                                                    let uu____14347 =
                                                      let uu____14352 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14353 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14352,
                                                        uu____14353) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14347 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14346 in
                                                quant xy uu____14345 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14336) in
                                            let uu____14362 =
                                              let uu____14377 =
                                                let uu____14390 =
                                                  let uu____14399 =
                                                    let uu____14400 =
                                                      let uu____14401 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14401 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14400 in
                                                  quant qx uu____14399 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14390) in
                                              [uu____14377] in
                                            uu____14323 :: uu____14362 in
                                          uu____14269 :: uu____14308 in
                                        uu____14215 :: uu____14254 in
                                      uu____14161 :: uu____14200 in
                                    uu____14107 :: uu____14146 in
                                  uu____14053 :: uu____14092 in
                                uu____14005 :: uu____14038 in
                              uu____13951 :: uu____13990 in
                            uu____13897 :: uu____13936 in
                          uu____13843 :: uu____13882 in
                        uu____13789 :: uu____13828 in
                      uu____13735 :: uu____13774 in
                    uu____13687 :: uu____13720 in
                  uu____13640 :: uu____13672 in
                let mk1 l v1 =
                  let uu____14615 =
                    let uu____14624 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14682  ->
                              match uu____14682 with
                              | (l',uu____14696) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14624
                      (FStar_Option.map
                         (fun uu____14756  ->
                            match uu____14756 with | (uu____14775,b) -> b v1)) in
                  FStar_All.pipe_right uu____14615 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14846  ->
                          match uu____14846 with
                          | (l',uu____14860) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14898 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14898 with
        | (xxsym,xx) ->
            let uu____14905 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14905 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14915 =
                   let uu____14922 =
                     let uu____14923 =
                       let uu____14934 =
                         let uu____14935 =
                           let uu____14940 =
                             let uu____14941 =
                               let uu____14946 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14946) in
                             FStar_SMTEncoding_Util.mkEq uu____14941 in
                           (xx_has_type, uu____14940) in
                         FStar_SMTEncoding_Util.mkImp uu____14935 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14934) in
                     FStar_SMTEncoding_Util.mkForall uu____14923 in
                   let uu____14971 =
                     let uu____14972 =
                       let uu____14973 =
                         let uu____14974 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14974 in
                       Prims.strcat module_name uu____14973 in
                     varops.mk_unique uu____14972 in
                   (uu____14922, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14971) in
                 FStar_SMTEncoding_Util.mkAssume uu____14915)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____15010 =
      let uu____15011 =
        let uu____15018 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____15018, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15011 in
    let uu____15021 =
      let uu____15024 =
        let uu____15025 =
          let uu____15032 =
            let uu____15033 =
              let uu____15044 =
                let uu____15045 =
                  let uu____15050 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15050) in
                FStar_SMTEncoding_Util.mkImp uu____15045 in
              ([[typing_pred]], [xx], uu____15044) in
            mkForall_fuel uu____15033 in
          (uu____15032, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15025 in
      [uu____15024] in
    uu____15010 :: uu____15021 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15092 =
      let uu____15093 =
        let uu____15100 =
          let uu____15101 =
            let uu____15112 =
              let uu____15117 =
                let uu____15120 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15120] in
              [uu____15117] in
            let uu____15125 =
              let uu____15126 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15126 tt in
            (uu____15112, [bb], uu____15125) in
          FStar_SMTEncoding_Util.mkForall uu____15101 in
        (uu____15100, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15093 in
    let uu____15147 =
      let uu____15150 =
        let uu____15151 =
          let uu____15158 =
            let uu____15159 =
              let uu____15170 =
                let uu____15171 =
                  let uu____15176 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15176) in
                FStar_SMTEncoding_Util.mkImp uu____15171 in
              ([[typing_pred]], [xx], uu____15170) in
            mkForall_fuel uu____15159 in
          (uu____15158, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15151 in
      [uu____15150] in
    uu____15092 :: uu____15147 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15226 =
        let uu____15227 =
          let uu____15234 =
            let uu____15237 =
              let uu____15240 =
                let uu____15243 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15244 =
                  let uu____15247 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15247] in
                uu____15243 :: uu____15244 in
              tt :: uu____15240 in
            tt :: uu____15237 in
          ("Prims.Precedes", uu____15234) in
        FStar_SMTEncoding_Util.mkApp uu____15227 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15226 in
    let precedes_y_x =
      let uu____15251 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15251 in
    let uu____15254 =
      let uu____15255 =
        let uu____15262 =
          let uu____15263 =
            let uu____15274 =
              let uu____15279 =
                let uu____15282 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15282] in
              [uu____15279] in
            let uu____15287 =
              let uu____15288 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15288 tt in
            (uu____15274, [bb], uu____15287) in
          FStar_SMTEncoding_Util.mkForall uu____15263 in
        (uu____15262, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15255 in
    let uu____15309 =
      let uu____15312 =
        let uu____15313 =
          let uu____15320 =
            let uu____15321 =
              let uu____15332 =
                let uu____15333 =
                  let uu____15338 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15338) in
                FStar_SMTEncoding_Util.mkImp uu____15333 in
              ([[typing_pred]], [xx], uu____15332) in
            mkForall_fuel uu____15321 in
          (uu____15320, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15313 in
      let uu____15363 =
        let uu____15366 =
          let uu____15367 =
            let uu____15374 =
              let uu____15375 =
                let uu____15386 =
                  let uu____15387 =
                    let uu____15392 =
                      let uu____15393 =
                        let uu____15396 =
                          let uu____15399 =
                            let uu____15402 =
                              let uu____15403 =
                                let uu____15408 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15409 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15408, uu____15409) in
                              FStar_SMTEncoding_Util.mkGT uu____15403 in
                            let uu____15410 =
                              let uu____15413 =
                                let uu____15414 =
                                  let uu____15419 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15420 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15419, uu____15420) in
                                FStar_SMTEncoding_Util.mkGTE uu____15414 in
                              let uu____15421 =
                                let uu____15424 =
                                  let uu____15425 =
                                    let uu____15430 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15431 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15430, uu____15431) in
                                  FStar_SMTEncoding_Util.mkLT uu____15425 in
                                [uu____15424] in
                              uu____15413 :: uu____15421 in
                            uu____15402 :: uu____15410 in
                          typing_pred_y :: uu____15399 in
                        typing_pred :: uu____15396 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15393 in
                    (uu____15392, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15387 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15386) in
              mkForall_fuel uu____15375 in
            (uu____15374,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15367 in
        [uu____15366] in
      uu____15312 :: uu____15363 in
    uu____15254 :: uu____15309 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15477 =
      let uu____15478 =
        let uu____15485 =
          let uu____15486 =
            let uu____15497 =
              let uu____15502 =
                let uu____15505 = FStar_SMTEncoding_Term.boxString b in
                [uu____15505] in
              [uu____15502] in
            let uu____15510 =
              let uu____15511 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15511 tt in
            (uu____15497, [bb], uu____15510) in
          FStar_SMTEncoding_Util.mkForall uu____15486 in
        (uu____15485, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15478 in
    let uu____15532 =
      let uu____15535 =
        let uu____15536 =
          let uu____15543 =
            let uu____15544 =
              let uu____15555 =
                let uu____15556 =
                  let uu____15561 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15561) in
                FStar_SMTEncoding_Util.mkImp uu____15556 in
              ([[typing_pred]], [xx], uu____15555) in
            mkForall_fuel uu____15544 in
          (uu____15543, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15536 in
      [uu____15535] in
    uu____15477 :: uu____15532 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15614 =
      let uu____15615 =
        let uu____15622 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15622, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15615 in
    [uu____15614] in
  let mk_and_interp env conj uu____15634 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15659 =
      let uu____15660 =
        let uu____15667 =
          let uu____15668 =
            let uu____15679 =
              let uu____15680 =
                let uu____15685 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15685, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15680 in
            ([[l_and_a_b]], [aa; bb], uu____15679) in
          FStar_SMTEncoding_Util.mkForall uu____15668 in
        (uu____15667, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15660 in
    [uu____15659] in
  let mk_or_interp env disj uu____15723 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15748 =
      let uu____15749 =
        let uu____15756 =
          let uu____15757 =
            let uu____15768 =
              let uu____15769 =
                let uu____15774 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15774, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15769 in
            ([[l_or_a_b]], [aa; bb], uu____15768) in
          FStar_SMTEncoding_Util.mkForall uu____15757 in
        (uu____15756, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15749 in
    [uu____15748] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15837 =
      let uu____15838 =
        let uu____15845 =
          let uu____15846 =
            let uu____15857 =
              let uu____15858 =
                let uu____15863 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15863, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15858 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15857) in
          FStar_SMTEncoding_Util.mkForall uu____15846 in
        (uu____15845, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15838 in
    [uu____15837] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____15936 =
      let uu____15937 =
        let uu____15944 =
          let uu____15945 =
            let uu____15956 =
              let uu____15957 =
                let uu____15962 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15962, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15957 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15956) in
          FStar_SMTEncoding_Util.mkForall uu____15945 in
        (uu____15944, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15937 in
    [uu____15936] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16033 =
      let uu____16034 =
        let uu____16041 =
          let uu____16042 =
            let uu____16053 =
              let uu____16054 =
                let uu____16059 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16059, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16054 in
            ([[l_imp_a_b]], [aa; bb], uu____16053) in
          FStar_SMTEncoding_Util.mkForall uu____16042 in
        (uu____16041, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16034 in
    [uu____16033] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16122 =
      let uu____16123 =
        let uu____16130 =
          let uu____16131 =
            let uu____16142 =
              let uu____16143 =
                let uu____16148 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16148, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16143 in
            ([[l_iff_a_b]], [aa; bb], uu____16142) in
          FStar_SMTEncoding_Util.mkForall uu____16131 in
        (uu____16130, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16123 in
    [uu____16122] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16200 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16200 in
    let uu____16203 =
      let uu____16204 =
        let uu____16211 =
          let uu____16212 =
            let uu____16223 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16223) in
          FStar_SMTEncoding_Util.mkForall uu____16212 in
        (uu____16211, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16204 in
    [uu____16203] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____16283 =
        let uu____16290 =
          let uu____16293 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16293] in
        ("Valid", uu____16290) in
      FStar_SMTEncoding_Util.mkApp uu____16283 in
    let uu____16296 =
      let uu____16297 =
        let uu____16304 =
          let uu____16305 =
            let uu____16316 =
              let uu____16317 =
                let uu____16322 =
                  let uu____16323 =
                    let uu____16334 =
                      let uu____16339 =
                        let uu____16342 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16342] in
                      [uu____16339] in
                    let uu____16347 =
                      let uu____16348 =
                        let uu____16353 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16353, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16348 in
                    (uu____16334, [xx1], uu____16347) in
                  FStar_SMTEncoding_Util.mkForall uu____16323 in
                (uu____16322, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16317 in
            ([[l_forall_a_b]], [aa; bb], uu____16316) in
          FStar_SMTEncoding_Util.mkForall uu____16305 in
        (uu____16304, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16297 in
    [uu____16296] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____16435 =
        let uu____16442 =
          let uu____16445 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16445] in
        ("Valid", uu____16442) in
      FStar_SMTEncoding_Util.mkApp uu____16435 in
    let uu____16448 =
      let uu____16449 =
        let uu____16456 =
          let uu____16457 =
            let uu____16468 =
              let uu____16469 =
                let uu____16474 =
                  let uu____16475 =
                    let uu____16486 =
                      let uu____16491 =
                        let uu____16494 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16494] in
                      [uu____16491] in
                    let uu____16499 =
                      let uu____16500 =
                        let uu____16505 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16505, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16500 in
                    (uu____16486, [xx1], uu____16499) in
                  FStar_SMTEncoding_Util.mkExists uu____16475 in
                (uu____16474, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16469 in
            ([[l_exists_a_b]], [aa; bb], uu____16468) in
          FStar_SMTEncoding_Util.mkForall uu____16457 in
        (uu____16456, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16449 in
    [uu____16448] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16565 =
      let uu____16566 =
        let uu____16573 =
          let uu____16574 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16574 range_ty in
        let uu____16575 = varops.mk_unique "typing_range_const" in
        (uu____16573, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16575) in
      FStar_SMTEncoding_Util.mkAssume uu____16566 in
    [uu____16565] in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____16609 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16609 x1 t in
      let uu____16610 =
        let uu____16621 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16621) in
      FStar_SMTEncoding_Util.mkForall uu____16610 in
    let uu____16644 =
      let uu____16645 =
        let uu____16652 =
          let uu____16653 =
            let uu____16664 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16664) in
          FStar_SMTEncoding_Util.mkForall uu____16653 in
        (uu____16652,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16645 in
    [uu____16644] in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e]) in
    let uu____16714 =
      let uu____16715 =
        let uu____16722 =
          let uu____16723 =
            let uu____16738 =
              let uu____16739 =
                let uu____16744 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____16745 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____16744, uu____16745) in
              FStar_SMTEncoding_Util.mkAnd uu____16739 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16738) in
          FStar_SMTEncoding_Util.mkForall' uu____16723 in
        (uu____16722,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____16715 in
    [uu____16714] in
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
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____17091 =
            FStar_Util.find_opt
              (fun uu____17117  ->
                 match uu____17117 with
                 | (l,uu____17129) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____17091 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17154,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17190 = encode_function_type_as_formula t env in
        match uu____17190 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu____17230 =
                ((let uu____17233 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17233) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17230
              then
                let uu____17240 = new_term_constant_and_tok_from_lid env lid in
                match uu____17240 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17259 =
                        let uu____17260 = FStar_Syntax_Subst.compress t_norm in
                        uu____17260.FStar_Syntax_Syntax.n in
                      match uu____17259 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17266) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17296  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17301 -> [] in
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    ([d; dd], env1)
              else
                (let uu____17315 = prims.is lid in
                 if uu____17315
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17323 = prims.mk lid vname in
                   match uu____17323 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17347 =
                      let uu____17358 = curried_arrow_formals_comp t_norm in
                      match uu____17358 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17376 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17376
                            then
                              let uu____17377 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___117_17380 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___117_17380.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___117_17380.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___117_17380.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___117_17380.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___117_17380.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___117_17380.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___117_17380.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___117_17380.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___117_17380.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___117_17380.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___117_17380.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___117_17380.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___117_17380.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___117_17380.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___117_17380.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___117_17380.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___117_17380.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___117_17380.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___117_17380.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___117_17380.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___117_17380.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___117_17380.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___117_17380.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___117_17380.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___117_17380.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___117_17380.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___117_17380.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___117_17380.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___117_17380.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___117_17380.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___117_17380.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___117_17380.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___117_17380.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17377
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17392 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17392)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17347 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17437 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17437 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17458 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___89_17500  ->
                                       match uu___89_17500 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17504 =
                                             FStar_Util.prefix vars in
                                           (match uu____17504 with
                                            | (uu____17525,(xxsym,uu____17527))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17545 =
                                                  let uu____17546 =
                                                    let uu____17553 =
                                                      let uu____17554 =
                                                        let uu____17565 =
                                                          let uu____17566 =
                                                            let uu____17571 =
                                                              let uu____17572
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17572 in
                                                            (vapp,
                                                              uu____17571) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17566 in
                                                        ([[vapp]], vars,
                                                          uu____17565) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17554 in
                                                    (uu____17553,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17546 in
                                                [uu____17545])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17591 =
                                             FStar_Util.prefix vars in
                                           (match uu____17591 with
                                            | (uu____17612,(xxsym,uu____17614))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  } in
                                                let tp_name =
                                                  mk_term_projector_name d f1 in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx]) in
                                                let uu____17637 =
                                                  let uu____17638 =
                                                    let uu____17645 =
                                                      let uu____17646 =
                                                        let uu____17657 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17657) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17646 in
                                                    (uu____17645,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17638 in
                                                [uu____17637])
                                       | uu____17674 -> [])) in
                             let uu____17675 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17675 with
                              | (vars,guards,env',decls1,uu____17702) ->
                                  let uu____17715 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17724 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17724, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17726 =
                                          encode_formula p env' in
                                        (match uu____17726 with
                                         | (g,ds) ->
                                             let uu____17737 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17737,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17715 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17750 =
                                           let uu____17757 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17757) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17750 in
                                       let uu____17766 =
                                         let vname_decl =
                                           let uu____17774 =
                                             let uu____17785 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17795  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17785,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17774 in
                                         let uu____17804 =
                                           let env2 =
                                             let uu___118_17810 = env1 in
                                             {
                                               bindings =
                                                 (uu___118_17810.bindings);
                                               depth = (uu___118_17810.depth);
                                               tcenv = (uu___118_17810.tcenv);
                                               warn = (uu___118_17810.warn);
                                               cache = (uu___118_17810.cache);
                                               nolabels =
                                                 (uu___118_17810.nolabels);
                                               use_zfuel_name =
                                                 (uu___118_17810.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___118_17810.current_module_name)
                                             } in
                                           let uu____17811 =
                                             let uu____17812 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17812 in
                                           if uu____17811
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17804 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17827::uu____17828 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort) in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff] in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)] in
                                                   let guarded_tok_typing =
                                                     let uu____17868 =
                                                       let uu____17879 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17879) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17868 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17906 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17909 =
                                               match formals with
                                               | [] ->
                                                   let uu____17926 =
                                                     let uu____17927 =
                                                       let uu____17930 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17930 in
                                                     push_free_var env1 lid
                                                       vname uu____17927 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17926)
                                               | uu____17935 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17942 =
                                                       let uu____17949 =
                                                         let uu____17950 =
                                                           let uu____17961 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17961) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17950 in
                                                       (uu____17949,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17942 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17909 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17766 with
                                        | (decls2,env2) ->
                                            let uu____18004 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____18012 =
                                                encode_term res_t1 env' in
                                              match uu____18012 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____18025 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____18025, decls) in
                                            (match uu____18004 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____18036 =
                                                     let uu____18043 =
                                                       let uu____18044 =
                                                         let uu____18055 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____18055) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____18044 in
                                                     (uu____18043,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____18036 in
                                                 let freshness =
                                                   let uu____18071 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____18071
                                                   then
                                                     let uu____18076 =
                                                       let uu____18077 =
                                                         let uu____18088 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____18099 =
                                                           varops.next_id () in
                                                         (vname, uu____18088,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____18099) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____18077 in
                                                     let uu____18102 =
                                                       let uu____18105 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____18105] in
                                                     uu____18076 ::
                                                       uu____18102
                                                   else [] in
                                                 let g =
                                                   let uu____18110 =
                                                     let uu____18113 =
                                                       let uu____18116 =
                                                         let uu____18119 =
                                                           let uu____18122 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____18122 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____18119 in
                                                       FStar_List.append
                                                         decls3 uu____18116 in
                                                     FStar_List.append decls2
                                                       uu____18113 in
                                                   FStar_List.append decls11
                                                     uu____18110 in
                                                 (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____18153 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18153 with
          | FStar_Pervasives_Native.None  ->
              let uu____18190 = encode_free_var false env x t t_norm [] in
              (match uu____18190 with
               | (decls,env1) ->
                   let uu____18217 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18217 with
                    | (n1,x',uu____18244) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18265) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t in
            let uu____18320 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18320 with
            | (decls,env1) ->
                let uu____18339 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18339
                then
                  let uu____18346 =
                    let uu____18349 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18349 in
                  (uu____18346, env1)
                else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18401  ->
                fun lb  ->
                  match uu____18401 with
                  | (decls,env1) ->
                      let uu____18421 =
                        let uu____18428 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18428
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18421 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18449 = FStar_Syntax_Util.head_and_args t in
    match uu____18449 with
    | (hd1,args) ->
        let uu____18486 =
          let uu____18487 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18487.FStar_Syntax_Syntax.n in
        (match uu____18486 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18491,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18510 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18532  ->
      fun quals  ->
        match uu____18532 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18608 = FStar_Util.first_N nbinders formals in
              match uu____18608 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18689  ->
                         fun uu____18690  ->
                           match (uu____18689, uu____18690) with
                           | ((formal,uu____18708),(binder,uu____18710)) ->
                               let uu____18719 =
                                 let uu____18726 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18726) in
                               FStar_Syntax_Syntax.NT uu____18719) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18734 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18765  ->
                              match uu____18765 with
                              | (x,i) ->
                                  let uu____18776 =
                                    let uu___119_18777 = x in
                                    let uu____18778 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___119_18777.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___119_18777.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18778
                                    } in
                                  (uu____18776, i))) in
                    FStar_All.pipe_right uu____18734
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18796 =
                      let uu____18797 = FStar_Syntax_Subst.compress body in
                      let uu____18798 =
                        let uu____18799 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18799 in
                      FStar_Syntax_Syntax.extend_app_n uu____18797
                        uu____18798 in
                    uu____18796 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18860 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18860
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___120_18863 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___120_18863.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___120_18863.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___120_18863.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___120_18863.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___120_18863.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___120_18863.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___120_18863.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___120_18863.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___120_18863.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___120_18863.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___120_18863.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___120_18863.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___120_18863.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___120_18863.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___120_18863.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___120_18863.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___120_18863.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___120_18863.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___120_18863.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___120_18863.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___120_18863.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___120_18863.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___120_18863.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___120_18863.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___120_18863.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___120_18863.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___120_18863.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___120_18863.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___120_18863.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___120_18863.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___120_18863.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___120_18863.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___120_18863.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18896 = FStar_Syntax_Util.abs_formals e in
                match uu____18896 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18960::uu____18961 ->
                         let uu____18976 =
                           let uu____18977 =
                             let uu____18980 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18980 in
                           uu____18977.FStar_Syntax_Syntax.n in
                         (match uu____18976 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19023 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19023 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____19065 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____19065
                                   then
                                     let uu____19100 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____19100 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19194  ->
                                                   fun uu____19195  ->
                                                     match (uu____19194,
                                                             uu____19195)
                                                     with
                                                     | ((x,uu____19213),
                                                        (b,uu____19215)) ->
                                                         let uu____19224 =
                                                           let uu____19231 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19231) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19224)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19233 =
                                            let uu____19254 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19254) in
                                          (uu____19233, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19322 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19322 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19411) ->
                              let uu____19416 =
                                let uu____19437 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19437 in
                              (uu____19416, true)
                          | uu____19502 when Prims.op_Negation norm1 ->
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
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____19504 ->
                              let uu____19505 =
                                let uu____19506 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19507 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19506
                                  uu____19507 in
                              failwith uu____19505)
                     | uu____19532 ->
                         let rec aux' t_norm2 =
                           let uu____19557 =
                             let uu____19558 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19558.FStar_Syntax_Syntax.n in
                           match uu____19557 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19599 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19599 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19627 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19627 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19707)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19712 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19768 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19768
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19780 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19874  ->
                            fun lb  ->
                              match uu____19874 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19969 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19969
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19972 =
                                      let uu____19987 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19987
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19972 with
                                    | (tok,decl,env2) ->
                                        let uu____20033 =
                                          let uu____20046 =
                                            let uu____20057 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____20057, tok) in
                                          uu____20046 :: toks in
                                        (uu____20033, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19780 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____20240 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20248 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20248 vars)
                            else
                              (let uu____20250 =
                                 let uu____20257 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20257) in
                               FStar_SMTEncoding_Util.mkApp uu____20250) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20339;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20341;
                             FStar_Syntax_Syntax.lbeff = uu____20342;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20405 =
                              let uu____20412 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20412 with
                              | (tcenv',uu____20430,e_t) ->
                                  let uu____20436 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20447 -> failwith "Impossible" in
                                  (match uu____20436 with
                                   | (e1,t_norm1) ->
                                       ((let uu___123_20463 = env2 in
                                         {
                                           bindings =
                                             (uu___123_20463.bindings);
                                           depth = (uu___123_20463.depth);
                                           tcenv = tcenv';
                                           warn = (uu___123_20463.warn);
                                           cache = (uu___123_20463.cache);
                                           nolabels =
                                             (uu___123_20463.nolabels);
                                           use_zfuel_name =
                                             (uu___123_20463.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___123_20463.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___123_20463.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20405 with
                             | (env',e1,t_norm1) ->
                                 let uu____20473 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20473 with
                                  | ((binders,body,uu____20494,uu____20495),curry)
                                      ->
                                      ((let uu____20506 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20506
                                        then
                                          let uu____20507 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20508 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20507 uu____20508
                                        else ());
                                       (let uu____20510 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20510 with
                                        | (vars,guards,env'1,binder_decls,uu____20537)
                                            ->
                                            let body1 =
                                              let uu____20551 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20551
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20554 =
                                              let uu____20563 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20563
                                              then
                                                let uu____20574 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20575 =
                                                  encode_formula body1 env'1 in
                                                (uu____20574, uu____20575)
                                              else
                                                (let uu____20585 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20585)) in
                                            (match uu____20554 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20608 =
                                                     let uu____20615 =
                                                       let uu____20616 =
                                                         let uu____20627 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20627) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20616 in
                                                     let uu____20638 =
                                                       let uu____20641 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20641 in
                                                     (uu____20615,
                                                       uu____20638,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20608 in
                                                 let uu____20644 =
                                                   let uu____20647 =
                                                     let uu____20650 =
                                                       let uu____20653 =
                                                         let uu____20656 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20656 in
                                                       FStar_List.append
                                                         decls2 uu____20653 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20650 in
                                                   FStar_List.append decls1
                                                     uu____20647 in
                                                 (uu____20644, env2))))))
                        | uu____20661 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20746 = varops.fresh "fuel" in
                          (uu____20746, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20749 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20837  ->
                                  fun uu____20838  ->
                                    match (uu____20837, uu____20838) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20986 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20986 in
                                        let gtok =
                                          let uu____20988 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20988 in
                                        let env4 =
                                          let uu____20990 =
                                            let uu____20993 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20993 in
                                          push_free_var env3 flid gtok
                                            uu____20990 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20749 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____21149 t_norm
                              uu____21151 =
                              match (uu____21149, uu____21151) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21195;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21196;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21224 =
                                    let uu____21231 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____21231 with
                                    | (tcenv',uu____21253,e_t) ->
                                        let uu____21259 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21270 ->
                                              failwith "Impossible" in
                                        (match uu____21259 with
                                         | (e1,t_norm1) ->
                                             ((let uu___124_21286 = env3 in
                                               {
                                                 bindings =
                                                   (uu___124_21286.bindings);
                                                 depth =
                                                   (uu___124_21286.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___124_21286.warn);
                                                 cache =
                                                   (uu___124_21286.cache);
                                                 nolabels =
                                                   (uu___124_21286.nolabels);
                                                 use_zfuel_name =
                                                   (uu___124_21286.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___124_21286.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___124_21286.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____21224 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21301 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21301
                                         then
                                           let uu____21302 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21303 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21304 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21302 uu____21303
                                             uu____21304
                                         else ());
                                        (let uu____21306 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21306 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21343 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21343
                                               then
                                                 let uu____21344 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21345 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21346 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21347 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21344 uu____21345
                                                   uu____21346 uu____21347
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21351 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21351 with
                                               | (vars,guards,env'1,binder_decls,uu____21382)
                                                   ->
                                                   let decl_g =
                                                     let uu____21396 =
                                                       let uu____21407 =
                                                         let uu____21410 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21410 in
                                                       (g, uu____21407,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21396 in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       flid g in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications")) in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars in
                                                   let app =
                                                     let uu____21435 =
                                                       let uu____21442 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21442) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21435 in
                                                   let gsapp =
                                                     let uu____21452 =
                                                       let uu____21459 =
                                                         let uu____21462 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21462 ::
                                                           vars_tm in
                                                       (g, uu____21459) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21452 in
                                                   let gmax =
                                                     let uu____21468 =
                                                       let uu____21475 =
                                                         let uu____21478 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21478 ::
                                                           vars_tm in
                                                       (g, uu____21475) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21468 in
                                                   let body1 =
                                                     let uu____21484 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21484
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21486 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21486 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21504 =
                                                            let uu____21511 =
                                                              let uu____21512
                                                                =
                                                                let uu____21527
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21527) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21512 in
                                                            let uu____21548 =
                                                              let uu____21551
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21551 in
                                                            (uu____21511,
                                                              uu____21548,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21504 in
                                                        let eqn_f =
                                                          let uu____21555 =
                                                            let uu____21562 =
                                                              let uu____21563
                                                                =
                                                                let uu____21574
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21574) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21563 in
                                                            (uu____21562,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21555 in
                                                        let eqn_g' =
                                                          let uu____21588 =
                                                            let uu____21595 =
                                                              let uu____21596
                                                                =
                                                                let uu____21607
                                                                  =
                                                                  let uu____21608
                                                                    =
                                                                    let uu____21613
                                                                    =
                                                                    let uu____21614
                                                                    =
                                                                    let uu____21621
                                                                    =
                                                                    let uu____21624
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21624
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21621) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21614 in
                                                                    (gsapp,
                                                                    uu____21613) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21608 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21607) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21596 in
                                                            (uu____21595,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21588 in
                                                        let uu____21647 =
                                                          let uu____21656 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21656
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21685)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____21710
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21710
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21715
                                                                  =
                                                                  let uu____21722
                                                                    =
                                                                    let uu____21723
                                                                    =
                                                                    let uu____21734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21734) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21723 in
                                                                  (uu____21722,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21715 in
                                                              let uu____21755
                                                                =
                                                                let uu____21762
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21762
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21775
                                                                    =
                                                                    let uu____21778
                                                                    =
                                                                    let uu____21779
                                                                    =
                                                                    let uu____21786
                                                                    =
                                                                    let uu____21787
                                                                    =
                                                                    let uu____21798
                                                                    =
                                                                    let uu____21799
                                                                    =
                                                                    let uu____21804
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21804,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21799 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21798) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21787 in
                                                                    (uu____21786,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21779 in
                                                                    [uu____21778] in
                                                                    (d3,
                                                                    uu____21775) in
                                                              (match uu____21755
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21647
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
                                                               env02)))))))) in
                            let uu____21869 =
                              let uu____21882 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21961  ->
                                   fun uu____21962  ->
                                     match (uu____21961, uu____21962) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____22117 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____22117 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21882 in
                            (match uu____21869 with
                             | (decls2,eqns,env01) ->
                                 let uu____22190 =
                                   let isDeclFun uu___90_22202 =
                                     match uu___90_22202 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22203 -> true
                                     | uu____22214 -> false in
                                   let uu____22215 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____22215
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____22190 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____22255 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___91_22259  ->
                                 match uu___91_22259 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22260 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22266 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22266))) in
                      if uu____22255
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks1 env1
                           else encode_rec_lbdefs bindings typs1 toks1 env1
                         with | Inner_let_rec  -> (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22318 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22318
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22367 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22367 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22371 = encode_sigelt' env se in
      match uu____22371 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22387 =
                  let uu____22388 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22388 in
                [uu____22387]
            | uu____22389 ->
                let uu____22390 =
                  let uu____22393 =
                    let uu____22394 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22394 in
                  uu____22393 :: g in
                let uu____22395 =
                  let uu____22398 =
                    let uu____22399 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22399 in
                  [uu____22398] in
                FStar_List.append uu____22390 uu____22395 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22412 =
          let uu____22413 = FStar_Syntax_Subst.compress t in
          uu____22413.FStar_Syntax_Syntax.n in
        match uu____22412 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22417)) -> s = "opaque_to_smt"
        | uu____22418 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22423 =
          let uu____22424 = FStar_Syntax_Subst.compress t in
          uu____22424.FStar_Syntax_Syntax.n in
        match uu____22423 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22428)) -> s = "uninterpreted_by_smt"
        | uu____22429 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22434 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22439 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22442 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22445 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22460 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22464 =
            let uu____22465 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22465 Prims.op_Negation in
          if uu____22464
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22491 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____22511 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22511 with
               | (aname,atok,env2) ->
                   let uu____22527 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22527 with
                    | (formals,uu____22545) ->
                        let uu____22558 =
                          let uu____22563 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22563 env2 in
                        (match uu____22558 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22575 =
                                 let uu____22576 =
                                   let uu____22587 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22603  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22587,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22576 in
                               [uu____22575;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22616 =
                               let aux uu____22668 uu____22669 =
                                 match (uu____22668, uu____22669) with
                                 | ((bv,uu____22721),(env3,acc_sorts,acc)) ->
                                     let uu____22759 = gen_term_var env3 bv in
                                     (match uu____22759 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22616 with
                              | (uu____22831,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22854 =
                                      let uu____22861 =
                                        let uu____22862 =
                                          let uu____22873 =
                                            let uu____22874 =
                                              let uu____22879 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22879) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22874 in
                                          ([[app]], xs_sorts, uu____22873) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22862 in
                                      (uu____22861,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22854 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22899 =
                                      let uu____22906 =
                                        let uu____22907 =
                                          let uu____22918 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22918) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22907 in
                                      (uu____22906,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22899 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22937 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22937 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22965,uu____22966)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22967 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22967 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22984,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22990 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___92_22994  ->
                      match uu___92_22994 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22995 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23000 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23001 -> false)) in
            Prims.op_Negation uu____22990 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____23010 =
               let uu____23017 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____23017 env fv t quals in
             match uu____23010 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____23032 =
                   let uu____23035 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____23035 in
                 (uu____23032, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23043 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____23043 with
           | (uu____23052,f1) ->
               let uu____23054 = encode_formula f1 env in
               (match uu____23054 with
                | (f2,decls) ->
                    let g =
                      let uu____23068 =
                        let uu____23069 =
                          let uu____23076 =
                            let uu____23079 =
                              let uu____23080 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____23080 in
                            FStar_Pervasives_Native.Some uu____23079 in
                          let uu____23081 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____23076, uu____23081) in
                        FStar_SMTEncoding_Util.mkAssume uu____23069 in
                      [uu____23068] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23087) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____23099 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23117 =
                       let uu____23120 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____23120.FStar_Syntax_Syntax.fv_name in
                     uu____23117.FStar_Syntax_Syntax.v in
                   let uu____23121 =
                     let uu____23122 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____23122 in
                   if uu____23121
                   then
                     let val_decl =
                       let uu___127_23150 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___127_23150.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___127_23150.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___127_23150.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____23155 = encode_sigelt' env1 val_decl in
                     match uu____23155 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____23099 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23183,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23185;
                          FStar_Syntax_Syntax.lbtyp = uu____23186;
                          FStar_Syntax_Syntax.lbeff = uu____23187;
                          FStar_Syntax_Syntax.lbdef = uu____23188;_}::[]),uu____23189)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23208 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23208 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____23237 =
                   let uu____23240 =
                     let uu____23241 =
                       let uu____23248 =
                         let uu____23249 =
                           let uu____23260 =
                             let uu____23261 =
                               let uu____23266 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23266) in
                             FStar_SMTEncoding_Util.mkEq uu____23261 in
                           ([[b2t_x]], [xx], uu____23260) in
                         FStar_SMTEncoding_Util.mkForall uu____23249 in
                       (uu____23248,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____23241 in
                   [uu____23240] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23237 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23299,uu____23300) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___93_23309  ->
                  match uu___93_23309 with
                  | FStar_Syntax_Syntax.Discriminator uu____23310 -> true
                  | uu____23311 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23314,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23325 =
                     let uu____23326 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23326.FStar_Ident.idText in
                   uu____23325 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___94_23330  ->
                     match uu___94_23330 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23331 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23335) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_23352  ->
                  match uu___95_23352 with
                  | FStar_Syntax_Syntax.Projector uu____23353 -> true
                  | uu____23358 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23361 = try_lookup_free_var env l in
          (match uu____23361 with
           | FStar_Pervasives_Native.Some uu____23368 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___128_23372 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___128_23372.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___128_23372.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___128_23372.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23379) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23397) ->
          let uu____23406 = encode_sigelts env ses in
          (match uu____23406 with
           | (g,env1) ->
               let uu____23423 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___96_23446  ->
                         match uu___96_23446 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23447;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23448;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23449;_}
                             -> false
                         | uu____23452 -> true)) in
               (match uu____23423 with
                | (g',inversions) ->
                    let uu____23467 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___97_23488  ->
                              match uu___97_23488 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23489 ->
                                  true
                              | uu____23500 -> false)) in
                    (match uu____23467 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23518,tps,k,uu____23521,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___98_23538  ->
                    match uu___98_23538 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23539 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23548 = c in
              match uu____23548 with
              | (name,args,uu____23553,uu____23554,uu____23555) ->
                  let uu____23560 =
                    let uu____23561 =
                      let uu____23572 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23589  ->
                                match uu____23589 with
                                | (uu____23596,sort,uu____23598) -> sort)) in
                      (name, uu____23572, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23561 in
                  [uu____23560]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23625 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23631 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23631 FStar_Option.isNone)) in
            if uu____23625
            then []
            else
              (let uu____23663 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23663 with
               | (xxsym,xx) ->
                   let uu____23672 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23711  ->
                             fun l  ->
                               match uu____23711 with
                               | (out,decls) ->
                                   let uu____23731 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23731 with
                                    | (uu____23742,data_t) ->
                                        let uu____23744 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23744 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23790 =
                                                 let uu____23791 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23791.FStar_Syntax_Syntax.n in
                                               match uu____23790 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23802,indices) ->
                                                   indices
                                               | uu____23824 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23848  ->
                                                         match uu____23848
                                                         with
                                                         | (x,uu____23854) ->
                                                             let uu____23855
                                                               =
                                                               let uu____23856
                                                                 =
                                                                 let uu____23863
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23863,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23856 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23855)
                                                    env) in
                                             let uu____23866 =
                                               encode_args indices env1 in
                                             (match uu____23866 with
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
                                                      let uu____23892 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23908
                                                                 =
                                                                 let uu____23913
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23913,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23908)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23892
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23916 =
                                                      let uu____23917 =
                                                        let uu____23922 =
                                                          let uu____23923 =
                                                            let uu____23928 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23928,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23923 in
                                                        (out, uu____23922) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23917 in
                                                    (uu____23916,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23672 with
                    | (data_ax,decls) ->
                        let uu____23941 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23941 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23952 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23952 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23956 =
                                 let uu____23963 =
                                   let uu____23964 =
                                     let uu____23975 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23990 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23975,
                                       uu____23990) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23964 in
                                 let uu____24005 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23963,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24005) in
                               FStar_SMTEncoding_Util.mkAssume uu____23956 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____24008 =
            let uu____24021 =
              let uu____24022 = FStar_Syntax_Subst.compress k in
              uu____24022.FStar_Syntax_Syntax.n in
            match uu____24021 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24067 -> (tps, k) in
          (match uu____24008 with
           | (formals,res) ->
               let uu____24090 = FStar_Syntax_Subst.open_term formals res in
               (match uu____24090 with
                | (formals1,res1) ->
                    let uu____24101 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____24101 with
                     | (vars,guards,env',binder_decls,uu____24126) ->
                         let uu____24139 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____24139 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____24158 =
                                  let uu____24165 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____24165) in
                                FStar_SMTEncoding_Util.mkApp uu____24158 in
                              let uu____24174 =
                                let tname_decl =
                                  let uu____24184 =
                                    let uu____24185 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24217  ->
                                              match uu____24217 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____24230 = varops.next_id () in
                                    (tname, uu____24185,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24230, false) in
                                  constructor_or_logic_type_decl uu____24184 in
                                let uu____24239 =
                                  match vars with
                                  | [] ->
                                      let uu____24252 =
                                        let uu____24253 =
                                          let uu____24256 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____24256 in
                                        push_free_var env1 t tname
                                          uu____24253 in
                                      ([], uu____24252)
                                  | uu____24263 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24272 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24272 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24286 =
                                          let uu____24293 =
                                            let uu____24294 =
                                              let uu____24309 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24309) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24294 in
                                          (uu____24293,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24286 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____24239 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____24174 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24349 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24349 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24367 =
                                               let uu____24368 =
                                                 let uu____24375 =
                                                   let uu____24376 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24376 in
                                                 (uu____24375,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24368 in
                                             [uu____24367]
                                           else [] in
                                         let uu____24380 =
                                           let uu____24383 =
                                             let uu____24386 =
                                               let uu____24387 =
                                                 let uu____24394 =
                                                   let uu____24395 =
                                                     let uu____24406 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24406) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24395 in
                                                 (uu____24394,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24387 in
                                             [uu____24386] in
                                           FStar_List.append karr uu____24383 in
                                         FStar_List.append decls1 uu____24380 in
                                   let aux =
                                     let uu____24422 =
                                       let uu____24425 =
                                         inversion_axioms tapp vars in
                                       let uu____24428 =
                                         let uu____24431 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24431] in
                                       FStar_List.append uu____24425
                                         uu____24428 in
                                     FStar_List.append kindingAx uu____24422 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24438,uu____24439,uu____24440,uu____24441,uu____24442)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24450,t,uu____24452,n_tps,uu____24454) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24462 = new_term_constant_and_tok_from_lid env d in
          (match uu____24462 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24479 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24479 with
                | (formals,t_res) ->
                    let uu____24514 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24514 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24528 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24528 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24598 =
                                            mk_term_projector_name d x in
                                          (uu____24598,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24600 =
                                  let uu____24619 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24619, true) in
                                FStar_All.pipe_right uu____24600
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____24658 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24658 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24670::uu____24671 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____24716 =
                                           let uu____24727 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24727) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24716
                                     | uu____24752 -> tok_typing in
                                   let uu____24761 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24761 with
                                    | (vars',guards',env'',decls_formals,uu____24786)
                                        ->
                                        let uu____24799 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____24799 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24830 ->
                                                   let uu____24837 =
                                                     let uu____24838 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24838 in
                                                   [uu____24837] in
                                             let encode_elim uu____24848 =
                                               let uu____24849 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24849 with
                                               | (head1,args) ->
                                                   let uu____24892 =
                                                     let uu____24893 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24893.FStar_Syntax_Syntax.n in
                                                   (match uu____24892 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24903;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24904;_},uu____24905)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24911 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24911
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
                                                                 | uu____24954
                                                                    ->
                                                                    let uu____24955
                                                                    =
                                                                    let uu____24960
                                                                    =
                                                                    let uu____24961
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24961 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24960) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24955
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24977
                                                                    =
                                                                    let uu____24978
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24978 in
                                                                    if
                                                                    uu____24977
                                                                    then
                                                                    let uu____24991
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24991]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24993
                                                               =
                                                               let uu____25006
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25056
                                                                     ->
                                                                    fun
                                                                    uu____25057
                                                                     ->
                                                                    match 
                                                                    (uu____25056,
                                                                    uu____25057)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25152
                                                                    =
                                                                    let uu____25159
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25159 in
                                                                    (match uu____25152
                                                                    with
                                                                    | 
                                                                    (uu____25172,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25180
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25180
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25182
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25182
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____25006 in
                                                             (match uu____24993
                                                              with
                                                              | (uu____25197,arg_vars,elim_eqns_or_guards,uu____25200)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25230
                                                                    =
                                                                    let uu____25237
                                                                    =
                                                                    let uu____25238
                                                                    =
                                                                    let uu____25249
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25260
                                                                    =
                                                                    let uu____25261
                                                                    =
                                                                    let uu____25266
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25266) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25261 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25249,
                                                                    uu____25260) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25238 in
                                                                    (uu____25237,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25230 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25289
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25289,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25291
                                                                    =
                                                                    let uu____25298
                                                                    =
                                                                    let uu____25299
                                                                    =
                                                                    let uu____25310
                                                                    =
                                                                    let uu____25315
                                                                    =
                                                                    let uu____25318
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25318] in
                                                                    [uu____25315] in
                                                                    let uu____25323
                                                                    =
                                                                    let uu____25324
                                                                    =
                                                                    let uu____25329
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25330
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25329,
                                                                    uu____25330) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25324 in
                                                                    (uu____25310,
                                                                    [x],
                                                                    uu____25323) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25299 in
                                                                    let uu____25349
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25298,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25349) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25291
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25356
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
                                                                    (let uu____25384
                                                                    =
                                                                    let uu____25385
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25385
                                                                    dapp1 in
                                                                    [uu____25384]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25356
                                                                    FStar_List.flatten in
                                                                    let uu____25392
                                                                    =
                                                                    let uu____25399
                                                                    =
                                                                    let uu____25400
                                                                    =
                                                                    let uu____25411
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25422
                                                                    =
                                                                    let uu____25423
                                                                    =
                                                                    let uu____25428
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25428) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25423 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25411,
                                                                    uu____25422) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25400 in
                                                                    (uu____25399,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25392) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25449 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25449
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
                                                                 | uu____25492
                                                                    ->
                                                                    let uu____25493
                                                                    =
                                                                    let uu____25498
                                                                    =
                                                                    let uu____25499
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25499 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25498) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25493
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25515
                                                                    =
                                                                    let uu____25516
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25516 in
                                                                    if
                                                                    uu____25515
                                                                    then
                                                                    let uu____25529
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25529]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25531
                                                               =
                                                               let uu____25544
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25594
                                                                     ->
                                                                    fun
                                                                    uu____25595
                                                                     ->
                                                                    match 
                                                                    (uu____25594,
                                                                    uu____25595)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25690
                                                                    =
                                                                    let uu____25697
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25697 in
                                                                    (match uu____25690
                                                                    with
                                                                    | 
                                                                    (uu____25710,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25718
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25718
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25720
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25720
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____25544 in
                                                             (match uu____25531
                                                              with
                                                              | (uu____25735,arg_vars,elim_eqns_or_guards,uu____25738)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25768
                                                                    =
                                                                    let uu____25775
                                                                    =
                                                                    let uu____25776
                                                                    =
                                                                    let uu____25787
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25798
                                                                    =
                                                                    let uu____25799
                                                                    =
                                                                    let uu____25804
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25804) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25799 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25787,
                                                                    uu____25798) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25776 in
                                                                    (uu____25775,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25768 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25827
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25827,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25829
                                                                    =
                                                                    let uu____25836
                                                                    =
                                                                    let uu____25837
                                                                    =
                                                                    let uu____25848
                                                                    =
                                                                    let uu____25853
                                                                    =
                                                                    let uu____25856
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25856] in
                                                                    [uu____25853] in
                                                                    let uu____25861
                                                                    =
                                                                    let uu____25862
                                                                    =
                                                                    let uu____25867
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25868
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25867,
                                                                    uu____25868) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25862 in
                                                                    (uu____25848,
                                                                    [x],
                                                                    uu____25861) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25837 in
                                                                    let uu____25887
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25836,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25887) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25829
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25894
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
                                                                    (let uu____25922
                                                                    =
                                                                    let uu____25923
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25923
                                                                    dapp1 in
                                                                    [uu____25922]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25894
                                                                    FStar_List.flatten in
                                                                    let uu____25930
                                                                    =
                                                                    let uu____25937
                                                                    =
                                                                    let uu____25938
                                                                    =
                                                                    let uu____25949
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25960
                                                                    =
                                                                    let uu____25961
                                                                    =
                                                                    let uu____25966
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25966) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25961 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25949,
                                                                    uu____25960) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25938 in
                                                                    (uu____25937,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25930) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25985 ->
                                                        ((let uu____25987 =
                                                            let uu____25992 =
                                                              let uu____25993
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25994
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25993
                                                                uu____25994 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25992) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25987);
                                                         ([], []))) in
                                             let uu____25999 = encode_elim () in
                                             (match uu____25999 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26019 =
                                                      let uu____26022 =
                                                        let uu____26025 =
                                                          let uu____26028 =
                                                            let uu____26031 =
                                                              let uu____26032
                                                                =
                                                                let uu____26043
                                                                  =
                                                                  let uu____26046
                                                                    =
                                                                    let uu____26047
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26047 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26046 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26043) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26032 in
                                                            [uu____26031] in
                                                          let uu____26052 =
                                                            let uu____26055 =
                                                              let uu____26058
                                                                =
                                                                let uu____26061
                                                                  =
                                                                  let uu____26064
                                                                    =
                                                                    let uu____26067
                                                                    =
                                                                    let uu____26070
                                                                    =
                                                                    let uu____26071
                                                                    =
                                                                    let uu____26078
                                                                    =
                                                                    let uu____26079
                                                                    =
                                                                    let uu____26090
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26090) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26079 in
                                                                    (uu____26078,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26071 in
                                                                    let uu____26103
                                                                    =
                                                                    let uu____26106
                                                                    =
                                                                    let uu____26107
                                                                    =
                                                                    let uu____26114
                                                                    =
                                                                    let uu____26115
                                                                    =
                                                                    let uu____26126
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____26137
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26126,
                                                                    uu____26137) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26115 in
                                                                    (uu____26114,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26107 in
                                                                    [uu____26106] in
                                                                    uu____26070
                                                                    ::
                                                                    uu____26103 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26067 in
                                                                  FStar_List.append
                                                                    uu____26064
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26061 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26058 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26055 in
                                                          FStar_List.append
                                                            uu____26028
                                                            uu____26052 in
                                                        FStar_List.append
                                                          decls3 uu____26025 in
                                                      FStar_List.append
                                                        decls2 uu____26022 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26019 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____26183  ->
              fun se  ->
                match uu____26183 with
                | (g,env1) ->
                    let uu____26203 = encode_sigelt env1 se in
                    (match uu____26203 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26260 =
        match uu____26260 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26292 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____26298 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26298
                   then
                     let uu____26299 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26300 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26301 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26299 uu____26300 uu____26301
                   else ());
                  (let uu____26303 = encode_term t1 env1 in
                   match uu____26303 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26319 =
                         let uu____26326 =
                           let uu____26327 =
                             let uu____26328 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26328
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26327 in
                         new_term_constant_from_string env1 x uu____26326 in
                       (match uu____26319 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26344 = FStar_Options.log_queries () in
                              if uu____26344
                              then
                                let uu____26347 =
                                  let uu____26348 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26349 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26350 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26348 uu____26349 uu____26350 in
                                FStar_Pervasives_Native.Some uu____26347
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26366,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26380 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26380 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26403,se,uu____26405) ->
                 let uu____26410 = encode_sigelt env1 se in
                 (match uu____26410 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26427,se) ->
                 let uu____26433 = encode_sigelt env1 se in
                 (match uu____26433 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26450 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26450 with | (uu____26473,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26485 'Auu____26486 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26486,'Auu____26485)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26554  ->
              match uu____26554 with
              | (l,uu____26566,uu____26567) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26613  ->
              match uu____26613 with
              | (l,uu____26627,uu____26628) ->
                  let uu____26637 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26638 =
                    let uu____26641 =
                      let uu____26642 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26642 in
                    [uu____26641] in
                  uu____26637 :: uu____26638)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26667 =
      let uu____26670 =
        let uu____26671 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26674 =
          let uu____26675 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26675 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26671;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26674
        } in
      [uu____26670] in
    FStar_ST.op_Colon_Equals last_env uu____26667
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26734 = FStar_ST.op_Bang last_env in
      match uu____26734 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26790 ->
          let uu___129_26793 = e in
          let uu____26794 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___129_26793.bindings);
            depth = (uu___129_26793.depth);
            tcenv;
            warn = (uu___129_26793.warn);
            cache = (uu___129_26793.cache);
            nolabels = (uu___129_26793.nolabels);
            use_zfuel_name = (uu___129_26793.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___129_26793.encode_non_total_function_typ);
            current_module_name = uu____26794
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26798 = FStar_ST.op_Bang last_env in
    match uu____26798 with
    | [] -> failwith "Empty env stack"
    | uu____26853::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26911  ->
    let uu____26912 = FStar_ST.op_Bang last_env in
    match uu____26912 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___130_26975 = hd1 in
          {
            bindings = (uu___130_26975.bindings);
            depth = (uu___130_26975.depth);
            tcenv = (uu___130_26975.tcenv);
            warn = (uu___130_26975.warn);
            cache = refs;
            nolabels = (uu___130_26975.nolabels);
            use_zfuel_name = (uu___130_26975.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___130_26975.encode_non_total_function_typ);
            current_module_name = (uu___130_26975.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____27030  ->
    let uu____27031 = FStar_ST.op_Bang last_env in
    match uu____27031 with
    | [] -> failwith "Popping an empty stack"
    | uu____27086::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____27179::uu____27180,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___131_27188 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___131_27188.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___131_27188.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___131_27188.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27189 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____27204 =
        let uu____27207 =
          let uu____27208 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____27208 in
        let uu____27209 = open_fact_db_tags env in uu____27207 :: uu____27209 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27204
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____27231 = encode_sigelt env se in
      match uu____27231 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____27267 = FStar_Options.log_queries () in
        if uu____27267
        then
          let uu____27270 =
            let uu____27271 =
              let uu____27272 =
                let uu____27273 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____27273 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____27272 in
            FStar_SMTEncoding_Term.Caption uu____27271 in
          uu____27270 :: decls
        else decls in
      (let uu____27284 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27284
       then
         let uu____27285 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27285
       else ());
      (let env =
         let uu____27288 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____27288 tcenv in
       let uu____27289 = encode_top_level_facts env se in
       match uu____27289 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27303 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____27303)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27315 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27315
       then
         let uu____27316 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27316
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27351  ->
                 fun se  ->
                   match uu____27351 with
                   | (g,env2) ->
                       let uu____27371 = encode_top_level_facts env2 se in
                       (match uu____27371 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27394 =
         encode_signature
           (let uu___132_27403 = env in
            {
              bindings = (uu___132_27403.bindings);
              depth = (uu___132_27403.depth);
              tcenv = (uu___132_27403.tcenv);
              warn = false;
              cache = (uu___132_27403.cache);
              nolabels = (uu___132_27403.nolabels);
              use_zfuel_name = (uu___132_27403.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___132_27403.encode_non_total_function_typ);
              current_module_name = (uu___132_27403.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27394 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27420 = FStar_Options.log_queries () in
             if uu____27420
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___133_27428 = env1 in
               {
                 bindings = (uu___133_27428.bindings);
                 depth = (uu___133_27428.depth);
                 tcenv = (uu___133_27428.tcenv);
                 warn = true;
                 cache = (uu___133_27428.cache);
                 nolabels = (uu___133_27428.nolabels);
                 use_zfuel_name = (uu___133_27428.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___133_27428.encode_non_total_function_typ);
                 current_module_name = (uu___133_27428.current_module_name)
               });
            (let uu____27430 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27430
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____27482 =
           let uu____27483 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27483.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27482);
        (let env =
           let uu____27485 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27485 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27497 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27532 = aux rest in
                 (match uu____27532 with
                  | (out,rest1) ->
                      let t =
                        let uu____27562 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27562 with
                        | FStar_Pervasives_Native.Some uu____27567 ->
                            let uu____27568 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27568
                              x.FStar_Syntax_Syntax.sort
                        | uu____27569 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27573 =
                        let uu____27576 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___134_27579 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_27579.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_27579.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27576 :: out in
                      (uu____27573, rest1))
             | uu____27584 -> ([], bindings1) in
           let uu____27591 = aux bindings in
           match uu____27591 with
           | (closing,bindings1) ->
               let uu____27616 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27616, bindings1) in
         match uu____27497 with
         | (q1,bindings1) ->
             let uu____27639 =
               let uu____27644 =
                 FStar_List.filter
                   (fun uu___99_27649  ->
                      match uu___99_27649 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27650 ->
                          false
                      | uu____27657 -> true) bindings1 in
               encode_env_bindings env uu____27644 in
             (match uu____27639 with
              | (env_decls,env1) ->
                  ((let uu____27675 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27675
                    then
                      let uu____27676 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27676
                    else ());
                   (let uu____27678 = encode_formula q1 env1 in
                    match uu____27678 with
                    | (phi,qdecls) ->
                        let uu____27699 =
                          let uu____27704 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27704 phi in
                        (match uu____27699 with
                         | (labels,phi1) ->
                             let uu____27721 = encode_labels labels in
                             (match uu____27721 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27758 =
                                      let uu____27765 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27766 =
                                        varops.mk_unique "@query" in
                                      (uu____27765,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27766) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27758 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))