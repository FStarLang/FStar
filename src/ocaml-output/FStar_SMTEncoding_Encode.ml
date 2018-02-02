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
      (fun uu___78_107  ->
         match uu___78_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___101_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___101_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___101_143.FStar_Syntax_Syntax.sort)
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
          (fun uu____772  ->
             match uu____772 with
             | (names1,uu____784) -> FStar_Util.smap_try_find names1 y1) in
      match uu____686 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____793 ->
          (FStar_Util.incr ctr;
           (let uu____828 =
              let uu____829 =
                let uu____830 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____830 in
              Prims.strcat "__" uu____829 in
            Prims.strcat y1 uu____828)) in
    let top_scope =
      let uu____875 =
        let uu____884 = FStar_ST.op_Bang scopes in FStar_List.hd uu____884 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____875 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____993 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1073 =
      let uu____1074 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1074 in
    FStar_Util.format2 "%s_%s" pfx uu____1073 in
  let string_const s =
    let uu____1079 =
      let uu____1082 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1082
        (fun uu____1165  ->
           match uu____1165 with
           | (uu____1176,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1079 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 () in
        let f =
          let uu____1189 = FStar_SMTEncoding_Util.mk_String_const id1 in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1189 in
        let top_scope =
          let uu____1193 =
            let uu____1202 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1202 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1193 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1300 =
    let uu____1301 =
      let uu____1312 = new_scope () in
      let uu____1321 = FStar_ST.op_Bang scopes in uu____1312 :: uu____1321 in
    FStar_ST.op_Colon_Equals scopes uu____1301 in
  let pop1 uu____1465 =
    let uu____1466 =
      let uu____1477 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1477 in
    FStar_ST.op_Colon_Equals scopes uu____1466 in
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
    let uu___102_1621 = x in
    let uu____1622 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1622;
      FStar_Syntax_Syntax.index = (uu___102_1621.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___102_1621.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1655 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1691 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____1738 'Auu____1739 .
    'Auu____1739 ->
      ('Auu____1739,'Auu____1738 FStar_Pervasives_Native.option)
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
  'Auu____2035 .
    'Auu____2035 ->
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
                 (fun uu___79_2069  ->
                    match uu___79_2069 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2073 -> [])) in
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
    let uu____2082 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___80_2092  ->
              match uu___80_2092 with
              | Binding_var (x,uu____2094) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2096,uu____2097,uu____2098) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2082 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2112 .
    env_t ->
      (binding -> 'Auu____2112 FStar_Pervasives_Native.option) ->
        'Auu____2112 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2140 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2140
      then
        let uu____2143 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2143
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
      let uu____2156 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2156)
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
        (let uu___103_2172 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___103_2172.tcenv);
           warn = (uu___103_2172.warn);
           cache = (uu___103_2172.cache);
           nolabels = (uu___103_2172.nolabels);
           use_zfuel_name = (uu___103_2172.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___103_2172.encode_non_total_function_typ);
           current_module_name = (uu___103_2172.current_module_name)
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
        (let uu___104_2190 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___104_2190.depth);
           tcenv = (uu___104_2190.tcenv);
           warn = (uu___104_2190.warn);
           cache = (uu___104_2190.cache);
           nolabels = (uu___104_2190.nolabels);
           use_zfuel_name = (uu___104_2190.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___104_2190.encode_non_total_function_typ);
           current_module_name = (uu___104_2190.current_module_name)
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
          (let uu___105_2211 = env in
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
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___106_2221 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___106_2221.depth);
          tcenv = (uu___106_2221.tcenv);
          warn = (uu___106_2221.warn);
          cache = (uu___106_2221.cache);
          nolabels = (uu___106_2221.nolabels);
          use_zfuel_name = (uu___106_2221.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___106_2221.encode_non_total_function_typ);
          current_module_name = (uu___106_2221.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___81_2245  ->
             match uu___81_2245 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2258 -> FStar_Pervasives_Native.None) in
      let uu____2263 = aux a in
      match uu____2263 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2275 = aux a2 in
          (match uu____2275 with
           | FStar_Pervasives_Native.None  ->
               let uu____2286 =
                 let uu____2287 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2288 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2287 uu____2288 in
               failwith uu____2286
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
      let uu____2315 =
        let uu___107_2316 = env in
        let uu____2317 =
          let uu____2320 =
            let uu____2321 =
              let uu____2334 =
                let uu____2337 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2337 in
              (x, fname, uu____2334, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2321 in
          uu____2320 :: (env.bindings) in
        {
          bindings = uu____2317;
          depth = (uu___107_2316.depth);
          tcenv = (uu___107_2316.tcenv);
          warn = (uu___107_2316.warn);
          cache = (uu___107_2316.cache);
          nolabels = (uu___107_2316.nolabels);
          use_zfuel_name = (uu___107_2316.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___107_2316.encode_non_total_function_typ);
          current_module_name = (uu___107_2316.current_module_name)
        } in
      (fname, ftok, uu____2315)
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
        (fun uu___82_2379  ->
           match uu___82_2379 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2418 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2435 =
        lookup_binding env
          (fun uu___83_2443  ->
             match uu___83_2443 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2458 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2435 FStar_Option.isSome
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
      let uu____2477 = try_lookup_lid env a in
      match uu____2477 with
      | FStar_Pervasives_Native.None  ->
          let uu____2510 =
            let uu____2511 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2511 in
          failwith uu____2510
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
          let uu___108_2559 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___108_2559.depth);
            tcenv = (uu___108_2559.tcenv);
            warn = (uu___108_2559.warn);
            cache = (uu___108_2559.cache);
            nolabels = (uu___108_2559.nolabels);
            use_zfuel_name = (uu___108_2559.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___108_2559.encode_non_total_function_typ);
            current_module_name = (uu___108_2559.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2573 = lookup_lid env x in
        match uu____2573 with
        | (t1,t2,uu____2586) ->
            let t3 =
              let uu____2596 =
                let uu____2603 =
                  let uu____2606 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2606] in
                (f, uu____2603) in
              FStar_SMTEncoding_Util.mkApp uu____2596 in
            let uu___109_2611 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___109_2611.depth);
              tcenv = (uu___109_2611.tcenv);
              warn = (uu___109_2611.warn);
              cache = (uu___109_2611.cache);
              nolabels = (uu___109_2611.nolabels);
              use_zfuel_name = (uu___109_2611.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___109_2611.encode_non_total_function_typ);
              current_module_name = (uu___109_2611.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2624 = try_lookup_lid env l in
      match uu____2624 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2673 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2681,fuel::[]) ->
                         let uu____2685 =
                           let uu____2686 =
                             let uu____2687 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2687
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2686 "fuel" in
                         if uu____2685
                         then
                           let uu____2690 =
                             let uu____2691 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2691
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2690
                         else FStar_Pervasives_Native.Some t
                     | uu____2695 -> FStar_Pervasives_Native.Some t)
                | uu____2696 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2709 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2709 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2713 =
            let uu____2714 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2714 in
          failwith uu____2713
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2725 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2725 with | (x,uu____2737,uu____2738) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2763 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2763 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2799;
                 FStar_SMTEncoding_Term.rng = uu____2800;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2815 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2839 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___84_2855  ->
           match uu___84_2855 with
           | Binding_fvar (uu____2858,nm',tok,uu____2861) when nm = nm' ->
               tok
           | uu____2870 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____2874 .
    'Auu____2874 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____2892  ->
      match uu____2892 with
      | (pats,vars,body) ->
          let fallback uu____2917 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____2922 = FStar_Options.unthrottle_inductives () in
          if uu____2922
          then fallback ()
          else
            (let uu____2924 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____2924 with
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
                           | uu____2955 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____2976 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____2976
                         | uu____2979 ->
                             let uu____2980 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____2980 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____2985 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3026 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3039 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3046 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3047 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3064 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3081 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3083 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3083 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3101;
             FStar_Syntax_Syntax.vars = uu____3102;_},uu____3103)
          ->
          let uu____3124 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3124 FStar_Option.isNone
      | uu____3141 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3148 =
        let uu____3149 = FStar_Syntax_Util.un_uinst t in
        uu____3149.FStar_Syntax_Syntax.n in
      match uu____3148 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3152,uu____3153,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___85_3174  ->
                  match uu___85_3174 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3175 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3177 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3177 FStar_Option.isSome
      | uu____3194 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3201 = head_normal env t in
      if uu____3201
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
    let uu____3212 =
      let uu____3213 = FStar_Syntax_Syntax.null_binder t in [uu____3213] in
    let uu____3214 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3212 uu____3214 FStar_Pervasives_Native.None
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
                    let uu____3252 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3252
                | s ->
                    let uu____3257 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3257) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___86_3272  ->
    match uu___86_3272 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3273 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3309;
                       FStar_SMTEncoding_Term.rng = uu____3310;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3333) ->
              let uu____3342 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3353 -> false) args (FStar_List.rev xs)) in
              if uu____3342
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3357,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3361 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3365 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3365)) in
              if uu____3361
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3369 -> FStar_Pervasives_Native.None in
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
    | uu____3591 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3595 -> false
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3614 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3627 ->
            let uu____3634 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3634
        | uu____3635 ->
            if norm1
            then let uu____3636 = whnf env t1 in aux false uu____3636
            else
              (let uu____3638 =
                 let uu____3639 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3640 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3639 uu____3640 in
               failwith uu____3638) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3672) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3677 ->
        let uu____3678 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3678)
let is_arithmetic_primitive:
  'Auu____3692 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3692 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3712::uu____3713::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3717::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3720 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3741 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3756 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____3760 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3760)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____3799)::uu____3800::uu____3801::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3852)::uu____3853::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____3890 -> false
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
          let uu____4109 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4109, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4112 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4112, [])
      | FStar_Const.Const_char c1 ->
          let uu____4116 =
            let uu____4117 =
              let uu____4124 =
                let uu____4127 =
                  let uu____4128 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4128 in
                [uu____4127] in
              ("FStar.Char.__char_of_int", uu____4124) in
            FStar_SMTEncoding_Util.mkApp uu____4117 in
          (uu____4116, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4144 =
            let uu____4145 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4145 in
          (uu____4144, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4166) ->
          let uu____4167 = varops.string_const s in (uu____4167, [])
      | FStar_Const.Const_range uu____4170 ->
          let uu____4171 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4171, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4177 =
            let uu____4178 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4178 in
          failwith uu____4177
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
        (let uu____4207 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4207
         then
           let uu____4208 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4208
         else ());
        (let uu____4210 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4294  ->
                   fun b  ->
                     match uu____4294 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4373 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4389 = gen_term_var env1 x in
                           match uu____4389 with
                           | (xxsym,xx,env') ->
                               let uu____4413 =
                                 let uu____4418 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4418 env1 xx in
                               (match uu____4413 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4373 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4210 with
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
          let uu____4577 = encode_term t env in
          match uu____4577 with
          | (t1,decls) ->
              let uu____4588 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4588, decls)
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
          let uu____4599 = encode_term t env in
          match uu____4599 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4614 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4614, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4616 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4616, decls))
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
        let uu____4622 = encode_args args_e env in
        match uu____4622 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4641 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4650 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4650 in
            let binary arg_tms1 =
              let uu____4663 =
                let uu____4664 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4664 in
              let uu____4665 =
                let uu____4666 =
                  let uu____4667 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4667 in
                FStar_SMTEncoding_Term.unboxInt uu____4666 in
              (uu____4663, uu____4665) in
            let mk_default uu____4673 =
              let uu____4674 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4674 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l a op mk_args ts =
              let uu____4720 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4720
              then
                let uu____4721 = let uu____4722 = mk_args ts in op uu____4722 in
                FStar_All.pipe_right uu____4721 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4751 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4751
              then
                let uu____4752 = binary ts in
                match uu____4752 with
                | (t1,t2) ->
                    let uu____4759 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____4759
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4763 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____4763
                 then
                   let uu____4764 = op (binary ts) in
                   FStar_All.pipe_right uu____4764
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 =
              mk_l ()
                (fun a412  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a412)
                (fun a413  -> (Obj.magic binary) a413) in
            let sub1 =
              mk_l ()
                (fun a414  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a414)
                (fun a415  -> (Obj.magic binary) a415) in
            let minus =
              mk_l ()
                (fun a416  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a416)
                (fun a417  -> (Obj.magic unary) a417) in
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
            let uu____4887 =
              let uu____4896 =
                FStar_List.tryFind
                  (fun uu____4918  ->
                     match uu____4918 with
                     | (l,uu____4928) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____4896 FStar_Util.must in
            (match uu____4887 with
             | (uu____4967,op) ->
                 let uu____4977 = op arg_tms in (uu____4977, decls))
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
        let uu____4985 = FStar_List.hd args_e in
        match uu____4985 with
        | (tm_sz,uu____4993) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5003 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5003 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5011 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5011);
                   t_decls) in
            let uu____5012 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5032::(sz_arg,uu____5034)::uu____5035::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5084 =
                    let uu____5087 = FStar_List.tail args_e in
                    FStar_List.tail uu____5087 in
                  let uu____5090 =
                    let uu____5093 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5093 in
                  (uu____5084, uu____5090)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5099::(sz_arg,uu____5101)::uu____5102::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5151 =
                    let uu____5152 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5152 in
                  failwith uu____5151
              | uu____5161 ->
                  let uu____5168 = FStar_List.tail args_e in
                  (uu____5168, FStar_Pervasives_Native.None) in
            (match uu____5012 with
             | (arg_tms,ext_sz) ->
                 let uu____5191 = encode_args arg_tms env in
                 (match uu____5191 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5212 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5221 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5221 in
                      let unary_arith arg_tms2 =
                        let uu____5230 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5230 in
                      let binary arg_tms2 =
                        let uu____5243 =
                          let uu____5244 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5244 in
                        let uu____5245 =
                          let uu____5246 =
                            let uu____5247 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5247 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5246 in
                        (uu____5243, uu____5245) in
                      let binary_arith arg_tms2 =
                        let uu____5262 =
                          let uu____5263 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5263 in
                        let uu____5264 =
                          let uu____5265 =
                            let uu____5266 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5266 in
                          FStar_SMTEncoding_Term.unboxInt uu____5265 in
                        (uu____5262, uu____5264) in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5308 =
                          let uu____5309 = mk_args ts in op uu____5309 in
                        FStar_All.pipe_right uu____5308 resBox in
                      let bv_and =
                        mk_bv ()
                          (fun a418  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a418)
                          (fun a419  -> (Obj.magic binary) a419)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv ()
                          (fun a420  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a420)
                          (fun a421  -> (Obj.magic binary) a421)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv ()
                          (fun a422  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a422)
                          (fun a423  -> (Obj.magic binary) a423)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv ()
                          (fun a424  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a424)
                          (fun a425  -> (Obj.magic binary) a425)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv ()
                          (fun a426  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a426)
                          (fun a427  -> (Obj.magic binary) a427)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv ()
                          (fun a428  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a428)
                          (fun a429  -> (Obj.magic binary_arith) a429)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv ()
                          (fun a430  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a430)
                          (fun a431  -> (Obj.magic binary_arith) a431)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv ()
                          (fun a432  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a432)
                          (fun a433  -> (Obj.magic binary_arith) a433)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv ()
                          (fun a434  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a434)
                          (fun a435  -> (Obj.magic binary_arith) a435)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv ()
                          (fun a436  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a436)
                          (fun a437  -> (Obj.magic binary_arith) a437)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv ()
                          (fun a438  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a438)
                          (fun a439  -> (Obj.magic binary) a439)
                          FStar_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu____5373 =
                          let uu____5376 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5376 in
                        let uu____5378 =
                          let uu____5381 =
                            let uu____5382 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5382 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5381 in
                        mk_bv () (fun a440  -> (Obj.magic uu____5373) a440)
                          (fun a441  -> (Obj.magic unary) a441) uu____5378
                          arg_tms2 in
                      let to_int1 =
                        mk_bv ()
                          (fun a442  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a442) (fun a443  -> (Obj.magic unary) a443)
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv ()
                          (fun a444  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a444)
                          (fun a445  -> (Obj.magic unary_arith) a445)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
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
                      let uu____5581 =
                        let uu____5590 =
                          FStar_List.tryFind
                            (fun uu____5612  ->
                               match uu____5612 with
                               | (l,uu____5622) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5590 FStar_Util.must in
                      (match uu____5581 with
                       | (uu____5663,op) ->
                           let uu____5673 = op arg_tms1 in
                           (uu____5673, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5684 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5684
       then
         let uu____5685 = FStar_Syntax_Print.tag_of_term t in
         let uu____5686 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5687 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5685 uu____5686
           uu____5687
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5693 ->
           let uu____5718 =
             let uu____5719 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5720 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5721 = FStar_Syntax_Print.term_to_string t0 in
             let uu____5722 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5719
               uu____5720 uu____5721 uu____5722 in
           failwith uu____5718
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5727 =
             let uu____5728 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5729 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5730 = FStar_Syntax_Print.term_to_string t0 in
             let uu____5731 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5728
               uu____5729 uu____5730 uu____5731 in
           failwith uu____5727
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5737 =
             let uu____5738 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5738 in
           failwith uu____5737
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____5745) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____5786;
              FStar_Syntax_Syntax.vars = uu____5787;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____5804 = varops.fresh "t" in
             (uu____5804, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____5807 =
               let uu____5818 =
                 let uu____5821 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____5821 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____5818) in
             FStar_SMTEncoding_Term.DeclFun uu____5807 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5829) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5839 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____5839, [])
       | FStar_Syntax_Syntax.Tm_type uu____5842 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5846) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____5871 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____5871 with
            | (binders1,res) ->
                let uu____5882 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____5882
                then
                  let uu____5887 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____5887 with
                   | (vars,guards,env',decls,uu____5912) ->
                       let fsym =
                         let uu____5930 = varops.fresh "f" in
                         (uu____5930, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____5933 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___110_5942 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___110_5942.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___110_5942.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___110_5942.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___110_5942.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___110_5942.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___110_5942.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___110_5942.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___110_5942.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___110_5942.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___110_5942.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___110_5942.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___110_5942.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___110_5942.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___110_5942.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___110_5942.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___110_5942.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___110_5942.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___110_5942.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___110_5942.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___110_5942.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___110_5942.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___110_5942.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___110_5942.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___110_5942.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___110_5942.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___110_5942.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___110_5942.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___110_5942.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___110_5942.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___110_5942.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___110_5942.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___110_5942.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___110_5942.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____5933 with
                        | (pre_opt,res_t) ->
                            let uu____5953 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____5953 with
                             | (res_pred,decls') ->
                                 let uu____5964 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5977 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____5977, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5981 =
                                         encode_formula pre env' in
                                       (match uu____5981 with
                                        | (guard,decls0) ->
                                            let uu____5994 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____5994, decls0)) in
                                 (match uu____5964 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6006 =
                                          let uu____6017 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6017) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6006 in
                                      let cvars =
                                        let uu____6035 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6035
                                          (FStar_List.filter
                                             (fun uu____6049  ->
                                                match uu____6049 with
                                                | (x,uu____6055) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6074 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6074 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6082 =
                                             let uu____6083 =
                                               let uu____6090 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6090) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6083 in
                                           (uu____6082,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6110 =
                                               let uu____6111 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6111 in
                                             varops.mk_unique uu____6110 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6122 =
                                               FStar_Options.log_queries () in
                                             if uu____6122
                                             then
                                               let uu____6125 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6125
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6133 =
                                               let uu____6140 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6140) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6133 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6152 =
                                               let uu____6159 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6159,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6152 in
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
                                             let uu____6180 =
                                               let uu____6187 =
                                                 let uu____6188 =
                                                   let uu____6199 =
                                                     let uu____6200 =
                                                       let uu____6205 =
                                                         let uu____6206 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6206 in
                                                       (f_has_t, uu____6205) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6200 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6199) in
                                                 mkForall_fuel uu____6188 in
                                               (uu____6187,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6180 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6229 =
                                               let uu____6236 =
                                                 let uu____6237 =
                                                   let uu____6248 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6248) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6237 in
                                               (uu____6236,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6229 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6273 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6273);
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
                     let uu____6288 =
                       let uu____6295 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6295,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6288 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6307 =
                       let uu____6314 =
                         let uu____6315 =
                           let uu____6326 =
                             let uu____6327 =
                               let uu____6332 =
                                 let uu____6333 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6333 in
                               (f_has_t, uu____6332) in
                             FStar_SMTEncoding_Util.mkImp uu____6327 in
                           ([[f_has_t]], [fsym], uu____6326) in
                         mkForall_fuel uu____6315 in
                       (uu____6314, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6307 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6360 ->
           let uu____6367 =
             let uu____6372 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6372 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6379;
                 FStar_Syntax_Syntax.vars = uu____6380;_} ->
                 let uu____6387 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6387 with
                  | (b,f1) ->
                      let uu____6412 =
                        let uu____6413 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6413 in
                      (uu____6412, f1))
             | uu____6422 -> failwith "impossible" in
           (match uu____6367 with
            | (x,f) ->
                let uu____6433 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6433 with
                 | (base_t,decls) ->
                     let uu____6444 = gen_term_var env x in
                     (match uu____6444 with
                      | (x1,xtm,env') ->
                          let uu____6458 = encode_formula f env' in
                          (match uu____6458 with
                           | (refinement,decls') ->
                               let uu____6469 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6469 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6485 =
                                        let uu____6488 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6495 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6488
                                          uu____6495 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6485 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6528  ->
                                              match uu____6528 with
                                              | (y,uu____6534) ->
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
                                    let uu____6567 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6567 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6575 =
                                           let uu____6576 =
                                             let uu____6583 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6583) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6576 in
                                         (uu____6575,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6604 =
                                             let uu____6605 =
                                               let uu____6606 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6606 in
                                             Prims.strcat module_name
                                               uu____6605 in
                                           varops.mk_unique uu____6604 in
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
                                           let uu____6620 =
                                             let uu____6627 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6627) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6620 in
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
                                           let uu____6642 =
                                             let uu____6649 =
                                               let uu____6650 =
                                                 let uu____6661 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6661) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6650 in
                                             (uu____6649,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6642 in
                                         let t_kinding =
                                           let uu____6679 =
                                             let uu____6686 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6686,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6679 in
                                         let t_interp =
                                           let uu____6704 =
                                             let uu____6711 =
                                               let uu____6712 =
                                                 let uu____6723 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6723) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6712 in
                                             let uu____6746 =
                                               let uu____6749 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6749 in
                                             (uu____6711, uu____6746,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6704 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____6756 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6756);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6786 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6786 in
           let uu____6787 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____6787 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6799 =
                    let uu____6806 =
                      let uu____6807 =
                        let uu____6808 =
                          let uu____6809 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6809 in
                        FStar_Util.format1 "uvar_typing_%s" uu____6808 in
                      varops.mk_unique uu____6807 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6806) in
                  FStar_SMTEncoding_Util.mkAssume uu____6799 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6814 ->
           let uu____6829 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____6829 with
            | (head1,args_e) ->
                let uu____6870 =
                  let uu____6883 =
                    let uu____6884 = FStar_Syntax_Subst.compress head1 in
                    uu____6884.FStar_Syntax_Syntax.n in
                  (uu____6883, args_e) in
                (match uu____6870 with
                 | uu____6899 when head_redex env head1 ->
                     let uu____6912 = whnf env t in
                     encode_term uu____6912 env
                 | uu____6913 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6932 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6946;
                       FStar_Syntax_Syntax.vars = uu____6947;_},uu____6948),uu____6949::
                    (v1,uu____6951)::(v2,uu____6953)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7004 = encode_term v1 env in
                     (match uu____7004 with
                      | (v11,decls1) ->
                          let uu____7015 = encode_term v2 env in
                          (match uu____7015 with
                           | (v21,decls2) ->
                               let uu____7026 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7026,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7030::(v1,uu____7032)::(v2,uu____7034)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7081 = encode_term v1 env in
                     (match uu____7081 with
                      | (v11,decls1) ->
                          let uu____7092 = encode_term v2 env in
                          (match uu____7092 with
                           | (v21,decls2) ->
                               let uu____7103 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7103,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7107)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7133)::(rng,uu____7135)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7170) ->
                     let e0 =
                       let uu____7188 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7188 in
                     ((let uu____7196 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7196
                       then
                         let uu____7197 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7197
                       else ());
                      (let e =
                         let uu____7202 =
                           let uu____7203 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7204 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7203
                             uu____7204 in
                         uu____7202 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7213),(arg,uu____7215)::[]) -> encode_term arg env
                 | uu____7240 ->
                     let uu____7253 = encode_args args_e env in
                     (match uu____7253 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7308 = encode_term head1 env in
                            match uu____7308 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7372 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7372 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7450  ->
                                                 fun uu____7451  ->
                                                   match (uu____7450,
                                                           uu____7451)
                                                   with
                                                   | ((bv,uu____7473),
                                                      (a,uu____7475)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7493 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7493
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7498 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7498 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7513 =
                                                   let uu____7520 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7529 =
                                                     let uu____7530 =
                                                       let uu____7531 =
                                                         let uu____7532 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7532 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7531 in
                                                     varops.mk_unique
                                                       uu____7530 in
                                                   (uu____7520,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7529) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7513 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7549 = lookup_free_var_sym env fv in
                            match uu____7549 with
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
                                   FStar_Syntax_Syntax.pos = uu____7580;
                                   FStar_Syntax_Syntax.vars = uu____7581;_},uu____7582)
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
                                   FStar_Syntax_Syntax.pos = uu____7593;
                                   FStar_Syntax_Syntax.vars = uu____7594;_},uu____7595)
                                ->
                                let uu____7600 =
                                  let uu____7601 =
                                    let uu____7606 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7606
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7601
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7600
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7636 =
                                  let uu____7637 =
                                    let uu____7642 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7642
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7637
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7636
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7671,(FStar_Util.Inl t1,uu____7673),uu____7674)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7723,(FStar_Util.Inr c,uu____7725),uu____7726)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7775 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7802 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7802 in
                               let uu____7803 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____7803 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7819;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7820;_},uu____7821)
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
                                     | uu____7835 ->
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
           let uu____7884 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____7884 with
            | (bs1,body1,opening) ->
                let fallback uu____7907 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____7914 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____7914, [decl]) in
                let is_impure rc =
                  let uu____7921 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____7921 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7931 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____7931
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____7951 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____7951
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____7955 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____7955)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7962 =
                         let uu____7967 =
                           let uu____7968 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7968 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7967) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7962);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7970 =
                       (is_impure rc) &&
                         (let uu____7972 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____7972) in
                     if uu____7970
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____7979 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____7979 with
                        | (vars,guards,envbody,decls,uu____8004) ->
                            let body2 =
                              let uu____8018 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8018
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8020 = encode_term body2 envbody in
                            (match uu____8020 with
                             | (body3,decls') ->
                                 let uu____8031 =
                                   let uu____8040 = codomain_eff rc in
                                   match uu____8040 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8059 = encode_term tfun env in
                                       (match uu____8059 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8031 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8091 =
                                          let uu____8102 =
                                            let uu____8103 =
                                              let uu____8108 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8108, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8103 in
                                          ([], vars, uu____8102) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8091 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8120 =
                                              let uu____8123 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8123
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8120 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8142 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8142 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8150 =
                                             let uu____8151 =
                                               let uu____8158 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8158) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8151 in
                                           (uu____8150,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8169 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8169 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8180 =
                                                    let uu____8181 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8181 = cache_size in
                                                  if uu____8180
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
                                                    let uu____8197 =
                                                      let uu____8198 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8198 in
                                                    varops.mk_unique
                                                      uu____8197 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8205 =
                                                    let uu____8212 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8212) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8205 in
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
                                                      let uu____8230 =
                                                        let uu____8231 =
                                                          let uu____8238 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8238,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8231 in
                                                      [uu____8230] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8251 =
                                                    let uu____8258 =
                                                      let uu____8259 =
                                                        let uu____8270 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8270) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8259 in
                                                    (uu____8258,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8251 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8287 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8287);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8290,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8291;
                          FStar_Syntax_Syntax.lbunivs = uu____8292;
                          FStar_Syntax_Syntax.lbtyp = uu____8293;
                          FStar_Syntax_Syntax.lbeff = uu____8294;
                          FStar_Syntax_Syntax.lbdef = uu____8295;_}::uu____8296),uu____8297)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8323;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8325;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8346 ->
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
              let uu____8416 = encode_term e1 env in
              match uu____8416 with
              | (ee1,decls1) ->
                  let uu____8427 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8427 with
                   | (xs,e21) ->
                       let uu____8452 = FStar_List.hd xs in
                       (match uu____8452 with
                        | (x1,uu____8466) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8468 = encode_body e21 env' in
                            (match uu____8468 with
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
            let uu____8500 =
              let uu____8507 =
                let uu____8508 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8508 in
              gen_term_var env uu____8507 in
            match uu____8500 with
            | (scrsym,scr',env1) ->
                let uu____8516 = encode_term e env1 in
                (match uu____8516 with
                 | (scr,decls) ->
                     let uu____8527 =
                       let encode_branch b uu____8552 =
                         match uu____8552 with
                         | (else_case,decls1) ->
                             let uu____8571 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8571 with
                              | (p,w,br) ->
                                  let uu____8597 = encode_pat env1 p in
                                  (match uu____8597 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8634  ->
                                                   match uu____8634 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8641 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8663 =
                                               encode_term w1 env2 in
                                             (match uu____8663 with
                                              | (w2,decls2) ->
                                                  let uu____8676 =
                                                    let uu____8677 =
                                                      let uu____8682 =
                                                        let uu____8683 =
                                                          let uu____8688 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8688) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8683 in
                                                      (guard, uu____8682) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8677 in
                                                  (uu____8676, decls2)) in
                                       (match uu____8641 with
                                        | (guard1,decls2) ->
                                            let uu____8701 =
                                              encode_br br env2 in
                                            (match uu____8701 with
                                             | (br1,decls3) ->
                                                 let uu____8714 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8714,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8527 with
                      | (match_tm,decls1) ->
                          let uu____8733 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____8733, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____8773 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____8773
       then
         let uu____8774 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8774
       else ());
      (let uu____8776 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____8776 with
       | (vars,pat_term) ->
           let uu____8793 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8846  ->
                     fun v1  ->
                       match uu____8846 with
                       | (env1,vars1) ->
                           let uu____8898 = gen_term_var env1 v1 in
                           (match uu____8898 with
                            | (xx,uu____8920,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____8793 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8999 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9000 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9001 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9009 = encode_const c env1 in
                      (match uu____9009 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9023::uu____9024 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9027 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9050 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9050 with
                        | (uu____9057,uu____9058::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9061 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9094  ->
                                  match uu____9094 with
                                  | (arg,uu____9102) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9108 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9108)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9135) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9166 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9189 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9233  ->
                                  match uu____9233 with
                                  | (arg,uu____9247) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9253 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9253)) in
                      FStar_All.pipe_right uu____9189 FStar_List.flatten in
                let pat_term1 uu____9281 = encode_term pat_term env1 in
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
      let uu____9291 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9329  ->
                fun uu____9330  ->
                  match (uu____9329, uu____9330) with
                  | ((tms,decls),(t,uu____9366)) ->
                      let uu____9387 = encode_term t env in
                      (match uu____9387 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9291 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9444 = FStar_Syntax_Util.list_elements e in
        match uu____9444 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9465 =
          let uu____9480 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9480 FStar_Syntax_Util.head_and_args in
        match uu____9465 with
        | (head1,args) ->
            let uu____9519 =
              let uu____9532 =
                let uu____9533 = FStar_Syntax_Util.un_uinst head1 in
                uu____9533.FStar_Syntax_Syntax.n in
              (uu____9532, args) in
            (match uu____9519 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9547,uu____9548)::(e,uu____9550)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9585 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9621 =
            let uu____9636 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9636 FStar_Syntax_Util.head_and_args in
          match uu____9621 with
          | (head1,args) ->
              let uu____9677 =
                let uu____9690 =
                  let uu____9691 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9691.FStar_Syntax_Syntax.n in
                (uu____9690, args) in
              (match uu____9677 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9708)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9735 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____9757 = smt_pat_or1 t1 in
            (match uu____9757 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9773 = list_elements1 e in
                 FStar_All.pipe_right uu____9773
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9791 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____9791
                           (FStar_List.map one_pat)))
             | uu____9802 ->
                 let uu____9807 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____9807])
        | uu____9828 ->
            let uu____9831 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____9831] in
      let uu____9852 =
        let uu____9871 =
          let uu____9872 = FStar_Syntax_Subst.compress t in
          uu____9872.FStar_Syntax_Syntax.n in
        match uu____9871 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9911 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____9911 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9954;
                        FStar_Syntax_Syntax.effect_name = uu____9955;
                        FStar_Syntax_Syntax.result_typ = uu____9956;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9958)::(post,uu____9960)::(pats,uu____9962)::[];
                        FStar_Syntax_Syntax.flags = uu____9963;_}
                      ->
                      let uu____10004 = lemma_pats pats in
                      (binders1, pre, post, uu____10004)
                  | uu____10021 -> failwith "impos"))
        | uu____10040 -> failwith "Impos" in
      match uu____9852 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___111_10088 = env in
            {
              bindings = (uu___111_10088.bindings);
              depth = (uu___111_10088.depth);
              tcenv = (uu___111_10088.tcenv);
              warn = (uu___111_10088.warn);
              cache = (uu___111_10088.cache);
              nolabels = (uu___111_10088.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___111_10088.encode_non_total_function_typ);
              current_module_name = (uu___111_10088.current_module_name)
            } in
          let uu____10089 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10089 with
           | (vars,guards,env2,decls,uu____10114) ->
               let uu____10127 =
                 let uu____10142 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10196 =
                             let uu____10207 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2)) in
                             FStar_All.pipe_right uu____10207
                               FStar_List.unzip in
                           match uu____10196 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10142 FStar_List.unzip in
               (match uu____10127 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___112_10359 = env2 in
                      {
                        bindings = (uu___112_10359.bindings);
                        depth = (uu___112_10359.depth);
                        tcenv = (uu___112_10359.tcenv);
                        warn = (uu___112_10359.warn);
                        cache = (uu___112_10359.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___112_10359.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___112_10359.encode_non_total_function_typ);
                        current_module_name =
                          (uu___112_10359.current_module_name)
                      } in
                    let uu____10360 =
                      let uu____10365 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10365 env3 in
                    (match uu____10360 with
                     | (pre1,decls'') ->
                         let uu____10372 =
                           let uu____10377 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10377 env3 in
                         (match uu____10372 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10387 =
                                let uu____10388 =
                                  let uu____10399 =
                                    let uu____10400 =
                                      let uu____10405 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10405, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10400 in
                                  (pats, vars, uu____10399) in
                                FStar_SMTEncoding_Util.mkForall uu____10388 in
                              (uu____10387, decls1)))))
and encode_smt_pattern:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let uu____10418 = FStar_Syntax_Util.head_and_args t in
      match uu____10418 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1 in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10477::(x,uu____10479)::(t1,uu____10481)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10528 = encode_term x env in
               (match uu____10528 with
                | (x1,decls) ->
                    let uu____10541 = encode_term t1 env in
                    (match uu____10541 with
                     | (t2,decls') ->
                         let uu____10554 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                         (uu____10554, (FStar_List.append decls decls'))))
           | uu____10557 -> encode_term t env)
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10580 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10580
        then
          let uu____10581 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10582 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10581 uu____10582
        else () in
      let enc f r l =
        let uu____10615 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10643 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10643 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10615 with
        | (decls,args) ->
            let uu____10672 =
              let uu___113_10673 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___113_10673.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___113_10673.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10672, decls) in
      let const_op f r uu____10704 =
        let uu____10717 = f r in (uu____10717, []) in
      let un_op f l =
        let uu____10736 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10736 in
      let bin_op f uu___87_10752 =
        match uu___87_10752 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10763 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10797 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10820  ->
                 match uu____10820 with
                 | (t,uu____10834) ->
                     let uu____10835 = encode_formula t env in
                     (match uu____10835 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10797 with
        | (decls,phis) ->
            let uu____10864 =
              let uu___114_10865 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10865.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10865.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10864, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10926  ->
               match uu____10926 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10945) -> false
                    | uu____10946 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10961 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____10961
        else
          (let uu____10975 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____10975 r rf) in
      let mk_imp1 r uu___88_11000 =
        match uu___88_11000 with
        | (lhs,uu____11006)::(rhs,uu____11008)::[] ->
            let uu____11035 = encode_formula rhs env in
            (match uu____11035 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11050) ->
                      (l1, decls1)
                  | uu____11055 ->
                      let uu____11056 = encode_formula lhs env in
                      (match uu____11056 with
                       | (l2,decls2) ->
                           let uu____11067 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11067, (FStar_List.append decls1 decls2)))))
        | uu____11070 -> failwith "impossible" in
      let mk_ite r uu___89_11091 =
        match uu___89_11091 with
        | (guard,uu____11097)::(_then,uu____11099)::(_else,uu____11101)::[]
            ->
            let uu____11138 = encode_formula guard env in
            (match uu____11138 with
             | (g,decls1) ->
                 let uu____11149 = encode_formula _then env in
                 (match uu____11149 with
                  | (t,decls2) ->
                      let uu____11160 = encode_formula _else env in
                      (match uu____11160 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11174 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11199 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11199 in
      let connectives =
        let uu____11217 =
          let uu____11230 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11230) in
        let uu____11247 =
          let uu____11262 =
            let uu____11275 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11275) in
          let uu____11292 =
            let uu____11307 =
              let uu____11322 =
                let uu____11335 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11335) in
              let uu____11352 =
                let uu____11367 =
                  let uu____11382 =
                    let uu____11395 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11395) in
                  [uu____11382;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11367 in
              uu____11322 :: uu____11352 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11307 in
          uu____11262 :: uu____11292 in
        uu____11217 :: uu____11247 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11716 = encode_formula phi' env in
            (match uu____11716 with
             | (phi2,decls) ->
                 let uu____11727 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11727, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11728 ->
            let uu____11735 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11735 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11774 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11774 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11786;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11788;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11809 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11809 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11856::(x,uu____11858)::(t,uu____11860)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11907 = encode_term x env in
                 (match uu____11907 with
                  | (x1,decls) ->
                      let uu____11918 = encode_term t env in
                      (match uu____11918 with
                       | (t1,decls') ->
                           let uu____11929 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11929, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11934)::(msg,uu____11936)::(phi2,uu____11938)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11983 =
                   let uu____11988 =
                     let uu____11989 = FStar_Syntax_Subst.compress r in
                     uu____11989.FStar_Syntax_Syntax.n in
                   let uu____11992 =
                     let uu____11993 = FStar_Syntax_Subst.compress msg in
                     uu____11993.FStar_Syntax_Syntax.n in
                   (uu____11988, uu____11992) in
                 (match uu____11983 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12002))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12008 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12015)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12040 when head_redex env head2 ->
                 let uu____12053 = whnf env phi1 in
                 encode_formula uu____12053 env
             | uu____12054 ->
                 let uu____12067 = encode_term phi1 env in
                 (match uu____12067 with
                  | (tt,decls) ->
                      let uu____12078 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___115_12081 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___115_12081.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___115_12081.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12078, decls)))
        | uu____12082 ->
            let uu____12083 = encode_term phi1 env in
            (match uu____12083 with
             | (tt,decls) ->
                 let uu____12094 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___116_12097 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___116_12097.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___116_12097.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12094, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12133 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12133 with
        | (vars,guards,env2,decls,uu____12172) ->
            let uu____12185 =
              let uu____12198 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12250 =
                          let uu____12261 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12301  ->
                                    match uu____12301 with
                                    | (t,uu____12315) ->
                                        encode_smt_pattern t
                                          (let uu___117_12321 = env2 in
                                           {
                                             bindings =
                                               (uu___117_12321.bindings);
                                             depth = (uu___117_12321.depth);
                                             tcenv = (uu___117_12321.tcenv);
                                             warn = (uu___117_12321.warn);
                                             cache = (uu___117_12321.cache);
                                             nolabels =
                                               (uu___117_12321.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___117_12321.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___117_12321.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12261 FStar_List.unzip in
                        match uu____12250 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12198 FStar_List.unzip in
            (match uu____12185 with
             | (pats,decls') ->
                 let uu____12430 = encode_formula body env2 in
                 (match uu____12430 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12462;
                             FStar_SMTEncoding_Term.rng = uu____12463;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12478 -> guards in
                      let uu____12483 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12483, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12543  ->
                   match uu____12543 with
                   | (x,uu____12549) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12557 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12569 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12569) uu____12557 tl1 in
             let uu____12572 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12599  ->
                       match uu____12599 with
                       | (b,uu____12605) ->
                           let uu____12606 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12606)) in
             (match uu____12572 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12612) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12626 =
                    let uu____12631 =
                      let uu____12632 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12632 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12631) in
                  FStar_Errors.log_issue pos uu____12626) in
       let uu____12633 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12633 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12642 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12700  ->
                     match uu____12700 with
                     | (l,uu____12714) -> FStar_Ident.lid_equals op l)) in
           (match uu____12642 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12747,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12787 = encode_q_body env vars pats body in
             match uu____12787 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12832 =
                     let uu____12843 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12843) in
                   FStar_SMTEncoding_Term.mkForall uu____12832
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12862 = encode_q_body env vars pats body in
             match uu____12862 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12906 =
                   let uu____12907 =
                     let uu____12918 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12918) in
                   FStar_SMTEncoding_Term.mkExists uu____12907
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12906, decls))))
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
  let uu____13011 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13011 with
  | (asym,a) ->
      let uu____13018 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13018 with
       | (xsym,x) ->
           let uu____13025 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13025 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13069 =
                      let uu____13080 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13080, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13069 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13106 =
                      let uu____13113 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13113) in
                    FStar_SMTEncoding_Util.mkApp uu____13106 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13126 =
                    let uu____13129 =
                      let uu____13132 =
                        let uu____13135 =
                          let uu____13136 =
                            let uu____13143 =
                              let uu____13144 =
                                let uu____13155 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13155) in
                              FStar_SMTEncoding_Util.mkForall uu____13144 in
                            (uu____13143, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13136 in
                        let uu____13172 =
                          let uu____13175 =
                            let uu____13176 =
                              let uu____13183 =
                                let uu____13184 =
                                  let uu____13195 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13195) in
                                FStar_SMTEncoding_Util.mkForall uu____13184 in
                              (uu____13183,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13176 in
                          [uu____13175] in
                        uu____13135 :: uu____13172 in
                      xtok_decl :: uu____13132 in
                    xname_decl :: uu____13129 in
                  (xtok1, uu____13126) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13286 =
                    let uu____13299 =
                      let uu____13308 =
                        let uu____13309 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13309 in
                      quant axy uu____13308 in
                    (FStar_Parser_Const.op_Eq, uu____13299) in
                  let uu____13318 =
                    let uu____13333 =
                      let uu____13346 =
                        let uu____13355 =
                          let uu____13356 =
                            let uu____13357 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13357 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13356 in
                        quant axy uu____13355 in
                      (FStar_Parser_Const.op_notEq, uu____13346) in
                    let uu____13366 =
                      let uu____13381 =
                        let uu____13394 =
                          let uu____13403 =
                            let uu____13404 =
                              let uu____13405 =
                                let uu____13410 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13411 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13410, uu____13411) in
                              FStar_SMTEncoding_Util.mkLT uu____13405 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13404 in
                          quant xy uu____13403 in
                        (FStar_Parser_Const.op_LT, uu____13394) in
                      let uu____13420 =
                        let uu____13435 =
                          let uu____13448 =
                            let uu____13457 =
                              let uu____13458 =
                                let uu____13459 =
                                  let uu____13464 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13465 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13464, uu____13465) in
                                FStar_SMTEncoding_Util.mkLTE uu____13459 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13458 in
                            quant xy uu____13457 in
                          (FStar_Parser_Const.op_LTE, uu____13448) in
                        let uu____13474 =
                          let uu____13489 =
                            let uu____13502 =
                              let uu____13511 =
                                let uu____13512 =
                                  let uu____13513 =
                                    let uu____13518 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13519 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13518, uu____13519) in
                                  FStar_SMTEncoding_Util.mkGT uu____13513 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13512 in
                              quant xy uu____13511 in
                            (FStar_Parser_Const.op_GT, uu____13502) in
                          let uu____13528 =
                            let uu____13543 =
                              let uu____13556 =
                                let uu____13565 =
                                  let uu____13566 =
                                    let uu____13567 =
                                      let uu____13572 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13573 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13572, uu____13573) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13567 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13566 in
                                quant xy uu____13565 in
                              (FStar_Parser_Const.op_GTE, uu____13556) in
                            let uu____13582 =
                              let uu____13597 =
                                let uu____13610 =
                                  let uu____13619 =
                                    let uu____13620 =
                                      let uu____13621 =
                                        let uu____13626 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13627 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13626, uu____13627) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13621 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13620 in
                                  quant xy uu____13619 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13610) in
                              let uu____13636 =
                                let uu____13651 =
                                  let uu____13664 =
                                    let uu____13673 =
                                      let uu____13674 =
                                        let uu____13675 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13675 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13674 in
                                    quant qx uu____13673 in
                                  (FStar_Parser_Const.op_Minus, uu____13664) in
                                let uu____13684 =
                                  let uu____13699 =
                                    let uu____13712 =
                                      let uu____13721 =
                                        let uu____13722 =
                                          let uu____13723 =
                                            let uu____13728 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13729 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13728, uu____13729) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13723 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13722 in
                                      quant xy uu____13721 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13712) in
                                  let uu____13738 =
                                    let uu____13753 =
                                      let uu____13766 =
                                        let uu____13775 =
                                          let uu____13776 =
                                            let uu____13777 =
                                              let uu____13782 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13783 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13782, uu____13783) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13777 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13776 in
                                        quant xy uu____13775 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13766) in
                                    let uu____13792 =
                                      let uu____13807 =
                                        let uu____13820 =
                                          let uu____13829 =
                                            let uu____13830 =
                                              let uu____13831 =
                                                let uu____13836 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13837 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13836, uu____13837) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13831 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13830 in
                                          quant xy uu____13829 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13820) in
                                      let uu____13846 =
                                        let uu____13861 =
                                          let uu____13874 =
                                            let uu____13883 =
                                              let uu____13884 =
                                                let uu____13885 =
                                                  let uu____13890 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13891 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13890, uu____13891) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13885 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13884 in
                                            quant xy uu____13883 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13874) in
                                        let uu____13900 =
                                          let uu____13915 =
                                            let uu____13928 =
                                              let uu____13937 =
                                                let uu____13938 =
                                                  let uu____13939 =
                                                    let uu____13944 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13945 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13944,
                                                      uu____13945) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13939 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13938 in
                                              quant xy uu____13937 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13928) in
                                          let uu____13954 =
                                            let uu____13969 =
                                              let uu____13982 =
                                                let uu____13991 =
                                                  let uu____13992 =
                                                    let uu____13993 =
                                                      let uu____13998 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____13999 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____13998,
                                                        uu____13999) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13993 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13992 in
                                                quant xy uu____13991 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13982) in
                                            let uu____14008 =
                                              let uu____14023 =
                                                let uu____14036 =
                                                  let uu____14045 =
                                                    let uu____14046 =
                                                      let uu____14047 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14047 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14046 in
                                                  quant qx uu____14045 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14036) in
                                              [uu____14023] in
                                            uu____13969 :: uu____14008 in
                                          uu____13915 :: uu____13954 in
                                        uu____13861 :: uu____13900 in
                                      uu____13807 :: uu____13846 in
                                    uu____13753 :: uu____13792 in
                                  uu____13699 :: uu____13738 in
                                uu____13651 :: uu____13684 in
                              uu____13597 :: uu____13636 in
                            uu____13543 :: uu____13582 in
                          uu____13489 :: uu____13528 in
                        uu____13435 :: uu____13474 in
                      uu____13381 :: uu____13420 in
                    uu____13333 :: uu____13366 in
                  uu____13286 :: uu____13318 in
                let mk1 l v1 =
                  let uu____14261 =
                    let uu____14270 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14328  ->
                              match uu____14328 with
                              | (l',uu____14342) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14270
                      (FStar_Option.map
                         (fun uu____14402  ->
                            match uu____14402 with | (uu____14421,b) -> b v1)) in
                  FStar_All.pipe_right uu____14261 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14492  ->
                          match uu____14492 with
                          | (l',uu____14506) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14544 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14544 with
        | (xxsym,xx) ->
            let uu____14551 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14551 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14561 =
                   let uu____14568 =
                     let uu____14569 =
                       let uu____14580 =
                         let uu____14581 =
                           let uu____14586 =
                             let uu____14587 =
                               let uu____14592 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14592) in
                             FStar_SMTEncoding_Util.mkEq uu____14587 in
                           (xx_has_type, uu____14586) in
                         FStar_SMTEncoding_Util.mkImp uu____14581 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14580) in
                     FStar_SMTEncoding_Util.mkForall uu____14569 in
                   let uu____14617 =
                     let uu____14618 =
                       let uu____14619 =
                         let uu____14620 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14620 in
                       Prims.strcat module_name uu____14619 in
                     varops.mk_unique uu____14618 in
                   (uu____14568, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14617) in
                 FStar_SMTEncoding_Util.mkAssume uu____14561)
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
    let uu____14656 =
      let uu____14657 =
        let uu____14664 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14664, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14657 in
    let uu____14667 =
      let uu____14670 =
        let uu____14671 =
          let uu____14678 =
            let uu____14679 =
              let uu____14690 =
                let uu____14691 =
                  let uu____14696 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14696) in
                FStar_SMTEncoding_Util.mkImp uu____14691 in
              ([[typing_pred]], [xx], uu____14690) in
            mkForall_fuel uu____14679 in
          (uu____14678, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14671 in
      [uu____14670] in
    uu____14656 :: uu____14667 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14738 =
      let uu____14739 =
        let uu____14746 =
          let uu____14747 =
            let uu____14758 =
              let uu____14763 =
                let uu____14766 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14766] in
              [uu____14763] in
            let uu____14771 =
              let uu____14772 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14772 tt in
            (uu____14758, [bb], uu____14771) in
          FStar_SMTEncoding_Util.mkForall uu____14747 in
        (uu____14746, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14739 in
    let uu____14793 =
      let uu____14796 =
        let uu____14797 =
          let uu____14804 =
            let uu____14805 =
              let uu____14816 =
                let uu____14817 =
                  let uu____14822 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14822) in
                FStar_SMTEncoding_Util.mkImp uu____14817 in
              ([[typing_pred]], [xx], uu____14816) in
            mkForall_fuel uu____14805 in
          (uu____14804, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14797 in
      [uu____14796] in
    uu____14738 :: uu____14793 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14872 =
        let uu____14873 =
          let uu____14880 =
            let uu____14883 =
              let uu____14886 =
                let uu____14889 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14890 =
                  let uu____14893 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14893] in
                uu____14889 :: uu____14890 in
              tt :: uu____14886 in
            tt :: uu____14883 in
          ("Prims.Precedes", uu____14880) in
        FStar_SMTEncoding_Util.mkApp uu____14873 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14872 in
    let precedes_y_x =
      let uu____14897 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14897 in
    let uu____14900 =
      let uu____14901 =
        let uu____14908 =
          let uu____14909 =
            let uu____14920 =
              let uu____14925 =
                let uu____14928 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14928] in
              [uu____14925] in
            let uu____14933 =
              let uu____14934 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14934 tt in
            (uu____14920, [bb], uu____14933) in
          FStar_SMTEncoding_Util.mkForall uu____14909 in
        (uu____14908, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14901 in
    let uu____14955 =
      let uu____14958 =
        let uu____14959 =
          let uu____14966 =
            let uu____14967 =
              let uu____14978 =
                let uu____14979 =
                  let uu____14984 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14984) in
                FStar_SMTEncoding_Util.mkImp uu____14979 in
              ([[typing_pred]], [xx], uu____14978) in
            mkForall_fuel uu____14967 in
          (uu____14966, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14959 in
      let uu____15009 =
        let uu____15012 =
          let uu____15013 =
            let uu____15020 =
              let uu____15021 =
                let uu____15032 =
                  let uu____15033 =
                    let uu____15038 =
                      let uu____15039 =
                        let uu____15042 =
                          let uu____15045 =
                            let uu____15048 =
                              let uu____15049 =
                                let uu____15054 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15055 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15054, uu____15055) in
                              FStar_SMTEncoding_Util.mkGT uu____15049 in
                            let uu____15056 =
                              let uu____15059 =
                                let uu____15060 =
                                  let uu____15065 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15066 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15065, uu____15066) in
                                FStar_SMTEncoding_Util.mkGTE uu____15060 in
                              let uu____15067 =
                                let uu____15070 =
                                  let uu____15071 =
                                    let uu____15076 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15077 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15076, uu____15077) in
                                  FStar_SMTEncoding_Util.mkLT uu____15071 in
                                [uu____15070] in
                              uu____15059 :: uu____15067 in
                            uu____15048 :: uu____15056 in
                          typing_pred_y :: uu____15045 in
                        typing_pred :: uu____15042 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15039 in
                    (uu____15038, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15033 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15032) in
              mkForall_fuel uu____15021 in
            (uu____15020,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15013 in
        [uu____15012] in
      uu____14958 :: uu____15009 in
    uu____14900 :: uu____14955 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15123 =
      let uu____15124 =
        let uu____15131 =
          let uu____15132 =
            let uu____15143 =
              let uu____15148 =
                let uu____15151 = FStar_SMTEncoding_Term.boxString b in
                [uu____15151] in
              [uu____15148] in
            let uu____15156 =
              let uu____15157 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15157 tt in
            (uu____15143, [bb], uu____15156) in
          FStar_SMTEncoding_Util.mkForall uu____15132 in
        (uu____15131, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15124 in
    let uu____15178 =
      let uu____15181 =
        let uu____15182 =
          let uu____15189 =
            let uu____15190 =
              let uu____15201 =
                let uu____15202 =
                  let uu____15207 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15207) in
                FStar_SMTEncoding_Util.mkImp uu____15202 in
              ([[typing_pred]], [xx], uu____15201) in
            mkForall_fuel uu____15190 in
          (uu____15189, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15182 in
      [uu____15181] in
    uu____15123 :: uu____15178 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15260 =
      let uu____15261 =
        let uu____15268 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15268, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15261 in
    [uu____15260] in
  let mk_and_interp env conj uu____15280 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15305 =
      let uu____15306 =
        let uu____15313 =
          let uu____15314 =
            let uu____15325 =
              let uu____15326 =
                let uu____15331 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15331, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15326 in
            ([[l_and_a_b]], [aa; bb], uu____15325) in
          FStar_SMTEncoding_Util.mkForall uu____15314 in
        (uu____15313, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15306 in
    [uu____15305] in
  let mk_or_interp env disj uu____15369 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15394 =
      let uu____15395 =
        let uu____15402 =
          let uu____15403 =
            let uu____15414 =
              let uu____15415 =
                let uu____15420 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15420, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15415 in
            ([[l_or_a_b]], [aa; bb], uu____15414) in
          FStar_SMTEncoding_Util.mkForall uu____15403 in
        (uu____15402, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15395 in
    [uu____15394] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15483 =
      let uu____15484 =
        let uu____15491 =
          let uu____15492 =
            let uu____15503 =
              let uu____15504 =
                let uu____15509 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15509, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15504 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15503) in
          FStar_SMTEncoding_Util.mkForall uu____15492 in
        (uu____15491, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15484 in
    [uu____15483] in
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
    let uu____15582 =
      let uu____15583 =
        let uu____15590 =
          let uu____15591 =
            let uu____15602 =
              let uu____15603 =
                let uu____15608 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15608, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15603 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15602) in
          FStar_SMTEncoding_Util.mkForall uu____15591 in
        (uu____15590, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15583 in
    [uu____15582] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15679 =
      let uu____15680 =
        let uu____15687 =
          let uu____15688 =
            let uu____15699 =
              let uu____15700 =
                let uu____15705 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15705, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15700 in
            ([[l_imp_a_b]], [aa; bb], uu____15699) in
          FStar_SMTEncoding_Util.mkForall uu____15688 in
        (uu____15687, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15680 in
    [uu____15679] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15768 =
      let uu____15769 =
        let uu____15776 =
          let uu____15777 =
            let uu____15788 =
              let uu____15789 =
                let uu____15794 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15794, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15789 in
            ([[l_iff_a_b]], [aa; bb], uu____15788) in
          FStar_SMTEncoding_Util.mkForall uu____15777 in
        (uu____15776, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15769 in
    [uu____15768] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15846 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15846 in
    let uu____15849 =
      let uu____15850 =
        let uu____15857 =
          let uu____15858 =
            let uu____15869 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15869) in
          FStar_SMTEncoding_Util.mkForall uu____15858 in
        (uu____15857, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15850 in
    [uu____15849] in
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
      let uu____15929 =
        let uu____15936 =
          let uu____15939 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15939] in
        ("Valid", uu____15936) in
      FStar_SMTEncoding_Util.mkApp uu____15929 in
    let uu____15942 =
      let uu____15943 =
        let uu____15950 =
          let uu____15951 =
            let uu____15962 =
              let uu____15963 =
                let uu____15968 =
                  let uu____15969 =
                    let uu____15980 =
                      let uu____15985 =
                        let uu____15988 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15988] in
                      [uu____15985] in
                    let uu____15993 =
                      let uu____15994 =
                        let uu____15999 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15999, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15994 in
                    (uu____15980, [xx1], uu____15993) in
                  FStar_SMTEncoding_Util.mkForall uu____15969 in
                (uu____15968, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15963 in
            ([[l_forall_a_b]], [aa; bb], uu____15962) in
          FStar_SMTEncoding_Util.mkForall uu____15951 in
        (uu____15950, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15943 in
    [uu____15942] in
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
      let uu____16081 =
        let uu____16088 =
          let uu____16091 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16091] in
        ("Valid", uu____16088) in
      FStar_SMTEncoding_Util.mkApp uu____16081 in
    let uu____16094 =
      let uu____16095 =
        let uu____16102 =
          let uu____16103 =
            let uu____16114 =
              let uu____16115 =
                let uu____16120 =
                  let uu____16121 =
                    let uu____16132 =
                      let uu____16137 =
                        let uu____16140 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16140] in
                      [uu____16137] in
                    let uu____16145 =
                      let uu____16146 =
                        let uu____16151 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16151, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16146 in
                    (uu____16132, [xx1], uu____16145) in
                  FStar_SMTEncoding_Util.mkExists uu____16121 in
                (uu____16120, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16115 in
            ([[l_exists_a_b]], [aa; bb], uu____16114) in
          FStar_SMTEncoding_Util.mkForall uu____16103 in
        (uu____16102, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16095 in
    [uu____16094] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16211 =
      let uu____16212 =
        let uu____16219 =
          let uu____16220 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16220 range_ty in
        let uu____16221 = varops.mk_unique "typing_range_const" in
        (uu____16219, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16221) in
      FStar_SMTEncoding_Util.mkAssume uu____16212 in
    [uu____16211] in
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
        let uu____16255 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16255 x1 t in
      let uu____16256 =
        let uu____16267 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16267) in
      FStar_SMTEncoding_Util.mkForall uu____16256 in
    let uu____16290 =
      let uu____16291 =
        let uu____16298 =
          let uu____16299 =
            let uu____16310 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16310) in
          FStar_SMTEncoding_Util.mkForall uu____16299 in
        (uu____16298,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16291 in
    [uu____16290] in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e]) in
    let uu____16360 =
      let uu____16361 =
        let uu____16368 =
          let uu____16369 =
            let uu____16384 =
              let uu____16385 =
                let uu____16390 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____16391 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____16390, uu____16391) in
              FStar_SMTEncoding_Util.mkAnd uu____16385 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16384) in
          FStar_SMTEncoding_Util.mkForall' uu____16369 in
        (uu____16368,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____16361 in
    [uu____16360] in
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
          let uu____16737 =
            FStar_Util.find_opt
              (fun uu____16763  ->
                 match uu____16763 with
                 | (l,uu____16775) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16737 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16800,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16836 = encode_function_type_as_formula t env in
        match uu____16836 with
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
              let uu____16876 =
                ((let uu____16879 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16879) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16876
              then
                let uu____16886 = new_term_constant_and_tok_from_lid env lid in
                match uu____16886 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16905 =
                        let uu____16906 = FStar_Syntax_Subst.compress t_norm in
                        uu____16906.FStar_Syntax_Syntax.n in
                      match uu____16905 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16912) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16942  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16947 -> [] in
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
                (let uu____16961 = prims.is lid in
                 if uu____16961
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16969 = prims.mk lid vname in
                   match uu____16969 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16993 =
                      let uu____17004 = curried_arrow_formals_comp t_norm in
                      match uu____17004 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17022 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17022
                            then
                              let uu____17023 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___118_17026 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___118_17026.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___118_17026.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___118_17026.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___118_17026.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___118_17026.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___118_17026.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___118_17026.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___118_17026.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___118_17026.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___118_17026.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___118_17026.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___118_17026.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___118_17026.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___118_17026.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___118_17026.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___118_17026.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___118_17026.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___118_17026.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___118_17026.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___118_17026.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___118_17026.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___118_17026.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___118_17026.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___118_17026.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___118_17026.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___118_17026.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___118_17026.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___118_17026.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___118_17026.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___118_17026.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___118_17026.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___118_17026.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___118_17026.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17023
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17038 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17038)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16993 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17083 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17083 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17104 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___90_17146  ->
                                       match uu___90_17146 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17150 =
                                             FStar_Util.prefix vars in
                                           (match uu____17150 with
                                            | (uu____17171,(xxsym,uu____17173))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17191 =
                                                  let uu____17192 =
                                                    let uu____17199 =
                                                      let uu____17200 =
                                                        let uu____17211 =
                                                          let uu____17212 =
                                                            let uu____17217 =
                                                              let uu____17218
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17218 in
                                                            (vapp,
                                                              uu____17217) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17212 in
                                                        ([[vapp]], vars,
                                                          uu____17211) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17200 in
                                                    (uu____17199,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17192 in
                                                [uu____17191])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17237 =
                                             FStar_Util.prefix vars in
                                           (match uu____17237 with
                                            | (uu____17258,(xxsym,uu____17260))
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
                                                let uu____17283 =
                                                  let uu____17284 =
                                                    let uu____17291 =
                                                      let uu____17292 =
                                                        let uu____17303 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17303) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17292 in
                                                    (uu____17291,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17284 in
                                                [uu____17283])
                                       | uu____17320 -> [])) in
                             let uu____17321 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17321 with
                              | (vars,guards,env',decls1,uu____17348) ->
                                  let uu____17361 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17370 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17370, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17372 =
                                          encode_formula p env' in
                                        (match uu____17372 with
                                         | (g,ds) ->
                                             let uu____17383 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17383,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17361 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17396 =
                                           let uu____17403 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17403) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17396 in
                                       let uu____17412 =
                                         let vname_decl =
                                           let uu____17420 =
                                             let uu____17431 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17441  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17431,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17420 in
                                         let uu____17450 =
                                           let env2 =
                                             let uu___119_17456 = env1 in
                                             {
                                               bindings =
                                                 (uu___119_17456.bindings);
                                               depth = (uu___119_17456.depth);
                                               tcenv = (uu___119_17456.tcenv);
                                               warn = (uu___119_17456.warn);
                                               cache = (uu___119_17456.cache);
                                               nolabels =
                                                 (uu___119_17456.nolabels);
                                               use_zfuel_name =
                                                 (uu___119_17456.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___119_17456.current_module_name)
                                             } in
                                           let uu____17457 =
                                             let uu____17458 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17458 in
                                           if uu____17457
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17450 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17473::uu____17474 ->
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
                                                     let uu____17514 =
                                                       let uu____17525 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17525) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17514 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17552 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17555 =
                                               match formals with
                                               | [] ->
                                                   let uu____17572 =
                                                     let uu____17573 =
                                                       let uu____17576 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17576 in
                                                     push_free_var env1 lid
                                                       vname uu____17573 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17572)
                                               | uu____17581 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17588 =
                                                       let uu____17595 =
                                                         let uu____17596 =
                                                           let uu____17607 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17607) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17596 in
                                                       (uu____17595,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17588 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17555 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17412 with
                                        | (decls2,env2) ->
                                            let uu____17650 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17658 =
                                                encode_term res_t1 env' in
                                              match uu____17658 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17671 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17671, decls) in
                                            (match uu____17650 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17682 =
                                                     let uu____17689 =
                                                       let uu____17690 =
                                                         let uu____17701 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17701) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17690 in
                                                     (uu____17689,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17682 in
                                                 let freshness =
                                                   let uu____17717 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17717
                                                   then
                                                     let uu____17722 =
                                                       let uu____17723 =
                                                         let uu____17734 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17745 =
                                                           varops.next_id () in
                                                         (vname, uu____17734,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17745) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17723 in
                                                     let uu____17748 =
                                                       let uu____17751 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17751] in
                                                     uu____17722 ::
                                                       uu____17748
                                                   else [] in
                                                 let g =
                                                   let uu____17756 =
                                                     let uu____17759 =
                                                       let uu____17762 =
                                                         let uu____17765 =
                                                           let uu____17768 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17768 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17765 in
                                                       FStar_List.append
                                                         decls3 uu____17762 in
                                                     FStar_List.append decls2
                                                       uu____17759 in
                                                   FStar_List.append decls11
                                                     uu____17756 in
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
          let uu____17799 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17799 with
          | FStar_Pervasives_Native.None  ->
              let uu____17836 = encode_free_var false env x t t_norm [] in
              (match uu____17836 with
               | (decls,env1) ->
                   let uu____17863 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17863 with
                    | (n1,x',uu____17890) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17911) ->
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
            let uu____17966 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17966 with
            | (decls,env1) ->
                let uu____17985 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17985
                then
                  let uu____17992 =
                    let uu____17995 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17995 in
                  (uu____17992, env1)
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
             (fun uu____18047  ->
                fun lb  ->
                  match uu____18047 with
                  | (decls,env1) ->
                      let uu____18067 =
                        let uu____18074 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18074
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18067 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18095 = FStar_Syntax_Util.head_and_args t in
    match uu____18095 with
    | (hd1,args) ->
        let uu____18132 =
          let uu____18133 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18133.FStar_Syntax_Syntax.n in
        (match uu____18132 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18137,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18156 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18178  ->
      fun quals  ->
        match uu____18178 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18254 = FStar_Util.first_N nbinders formals in
              match uu____18254 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18335  ->
                         fun uu____18336  ->
                           match (uu____18335, uu____18336) with
                           | ((formal,uu____18354),(binder,uu____18356)) ->
                               let uu____18365 =
                                 let uu____18372 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18372) in
                               FStar_Syntax_Syntax.NT uu____18365) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18380 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18411  ->
                              match uu____18411 with
                              | (x,i) ->
                                  let uu____18422 =
                                    let uu___120_18423 = x in
                                    let uu____18424 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___120_18423.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___120_18423.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18424
                                    } in
                                  (uu____18422, i))) in
                    FStar_All.pipe_right uu____18380
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18442 =
                      let uu____18443 = FStar_Syntax_Subst.compress body in
                      let uu____18444 =
                        let uu____18445 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18445 in
                      FStar_Syntax_Syntax.extend_app_n uu____18443
                        uu____18444 in
                    uu____18442 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18506 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18506
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___121_18509 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___121_18509.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___121_18509.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___121_18509.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___121_18509.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___121_18509.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___121_18509.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___121_18509.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___121_18509.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___121_18509.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___121_18509.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___121_18509.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___121_18509.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___121_18509.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___121_18509.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___121_18509.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___121_18509.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___121_18509.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___121_18509.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___121_18509.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___121_18509.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___121_18509.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___121_18509.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___121_18509.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___121_18509.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___121_18509.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___121_18509.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___121_18509.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___121_18509.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___121_18509.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___121_18509.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___121_18509.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___121_18509.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___121_18509.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18542 = FStar_Syntax_Util.abs_formals e in
                match uu____18542 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18606::uu____18607 ->
                         let uu____18622 =
                           let uu____18623 =
                             let uu____18626 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18626 in
                           uu____18623.FStar_Syntax_Syntax.n in
                         (match uu____18622 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18669 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18669 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18711 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18711
                                   then
                                     let uu____18746 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18746 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18840  ->
                                                   fun uu____18841  ->
                                                     match (uu____18840,
                                                             uu____18841)
                                                     with
                                                     | ((x,uu____18859),
                                                        (b,uu____18861)) ->
                                                         let uu____18870 =
                                                           let uu____18877 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18877) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18870)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18879 =
                                            let uu____18900 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18900) in
                                          (uu____18879, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18968 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18968 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19057) ->
                              let uu____19062 =
                                let uu____19083 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19083 in
                              (uu____19062, true)
                          | uu____19148 when Prims.op_Negation norm1 ->
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
                          | uu____19150 ->
                              let uu____19151 =
                                let uu____19152 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19153 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19152
                                  uu____19153 in
                              failwith uu____19151)
                     | uu____19178 ->
                         let rec aux' t_norm2 =
                           let uu____19203 =
                             let uu____19204 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19204.FStar_Syntax_Syntax.n in
                           match uu____19203 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19245 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19245 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19273 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19273 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19353)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19358 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19414 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19414
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19426 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19520  ->
                            fun lb  ->
                              match uu____19520 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19615 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19615
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19618 =
                                      let uu____19633 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19633
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19618 with
                                    | (tok,decl,env2) ->
                                        let uu____19679 =
                                          let uu____19692 =
                                            let uu____19703 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19703, tok) in
                                          uu____19692 :: toks in
                                        (uu____19679, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19426 with
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
                        | uu____19886 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19894 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19894 vars)
                            else
                              (let uu____19896 =
                                 let uu____19903 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19903) in
                               FStar_SMTEncoding_Util.mkApp uu____19896) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19985;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19987;
                             FStar_Syntax_Syntax.lbeff = uu____19988;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20051 =
                              let uu____20058 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20058 with
                              | (tcenv',uu____20076,e_t) ->
                                  let uu____20082 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20093 -> failwith "Impossible" in
                                  (match uu____20082 with
                                   | (e1,t_norm1) ->
                                       ((let uu___124_20109 = env2 in
                                         {
                                           bindings =
                                             (uu___124_20109.bindings);
                                           depth = (uu___124_20109.depth);
                                           tcenv = tcenv';
                                           warn = (uu___124_20109.warn);
                                           cache = (uu___124_20109.cache);
                                           nolabels =
                                             (uu___124_20109.nolabels);
                                           use_zfuel_name =
                                             (uu___124_20109.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___124_20109.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___124_20109.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20051 with
                             | (env',e1,t_norm1) ->
                                 let uu____20119 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20119 with
                                  | ((binders,body,uu____20140,uu____20141),curry)
                                      ->
                                      ((let uu____20152 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20152
                                        then
                                          let uu____20153 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20154 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20153 uu____20154
                                        else ());
                                       (let uu____20156 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20156 with
                                        | (vars,guards,env'1,binder_decls,uu____20183)
                                            ->
                                            let body1 =
                                              let uu____20197 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20197
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20200 =
                                              let uu____20209 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20209
                                              then
                                                let uu____20220 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20221 =
                                                  encode_formula body1 env'1 in
                                                (uu____20220, uu____20221)
                                              else
                                                (let uu____20231 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20231)) in
                                            (match uu____20200 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20254 =
                                                     let uu____20261 =
                                                       let uu____20262 =
                                                         let uu____20273 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20273) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20262 in
                                                     let uu____20284 =
                                                       let uu____20287 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20287 in
                                                     (uu____20261,
                                                       uu____20284,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20254 in
                                                 let uu____20290 =
                                                   let uu____20293 =
                                                     let uu____20296 =
                                                       let uu____20299 =
                                                         let uu____20302 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20302 in
                                                       FStar_List.append
                                                         decls2 uu____20299 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20296 in
                                                   FStar_List.append decls1
                                                     uu____20293 in
                                                 (uu____20290, env2))))))
                        | uu____20307 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20392 = varops.fresh "fuel" in
                          (uu____20392, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20395 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20483  ->
                                  fun uu____20484  ->
                                    match (uu____20483, uu____20484) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20632 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20632 in
                                        let gtok =
                                          let uu____20634 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20634 in
                                        let env4 =
                                          let uu____20636 =
                                            let uu____20639 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20639 in
                                          push_free_var env3 flid gtok
                                            uu____20636 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20395 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20795 t_norm
                              uu____20797 =
                              match (uu____20795, uu____20797) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20841;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20842;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20870 =
                                    let uu____20877 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20877 with
                                    | (tcenv',uu____20899,e_t) ->
                                        let uu____20905 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20916 ->
                                              failwith "Impossible" in
                                        (match uu____20905 with
                                         | (e1,t_norm1) ->
                                             ((let uu___125_20932 = env3 in
                                               {
                                                 bindings =
                                                   (uu___125_20932.bindings);
                                                 depth =
                                                   (uu___125_20932.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___125_20932.warn);
                                                 cache =
                                                   (uu___125_20932.cache);
                                                 nolabels =
                                                   (uu___125_20932.nolabels);
                                                 use_zfuel_name =
                                                   (uu___125_20932.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___125_20932.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___125_20932.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20870 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20947 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20947
                                         then
                                           let uu____20948 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20949 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20950 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20948 uu____20949
                                             uu____20950
                                         else ());
                                        (let uu____20952 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20952 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20989 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20989
                                               then
                                                 let uu____20990 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20991 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20992 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20993 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20990 uu____20991
                                                   uu____20992 uu____20993
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20997 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20997 with
                                               | (vars,guards,env'1,binder_decls,uu____21028)
                                                   ->
                                                   let decl_g =
                                                     let uu____21042 =
                                                       let uu____21053 =
                                                         let uu____21056 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21056 in
                                                       (g, uu____21053,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21042 in
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
                                                     let uu____21081 =
                                                       let uu____21088 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21088) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21081 in
                                                   let gsapp =
                                                     let uu____21098 =
                                                       let uu____21105 =
                                                         let uu____21108 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21108 ::
                                                           vars_tm in
                                                       (g, uu____21105) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21098 in
                                                   let gmax =
                                                     let uu____21114 =
                                                       let uu____21121 =
                                                         let uu____21124 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21124 ::
                                                           vars_tm in
                                                       (g, uu____21121) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21114 in
                                                   let body1 =
                                                     let uu____21130 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21130
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21132 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21132 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21150 =
                                                            let uu____21157 =
                                                              let uu____21158
                                                                =
                                                                let uu____21173
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
                                                                  uu____21173) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21158 in
                                                            let uu____21194 =
                                                              let uu____21197
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21197 in
                                                            (uu____21157,
                                                              uu____21194,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21150 in
                                                        let eqn_f =
                                                          let uu____21201 =
                                                            let uu____21208 =
                                                              let uu____21209
                                                                =
                                                                let uu____21220
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21220) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21209 in
                                                            (uu____21208,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21201 in
                                                        let eqn_g' =
                                                          let uu____21234 =
                                                            let uu____21241 =
                                                              let uu____21242
                                                                =
                                                                let uu____21253
                                                                  =
                                                                  let uu____21254
                                                                    =
                                                                    let uu____21259
                                                                    =
                                                                    let uu____21260
                                                                    =
                                                                    let uu____21267
                                                                    =
                                                                    let uu____21270
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21270
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21267) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21260 in
                                                                    (gsapp,
                                                                    uu____21259) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21254 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21253) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21242 in
                                                            (uu____21241,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21234 in
                                                        let uu____21293 =
                                                          let uu____21302 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21302
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21331)
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
                                                                  let uu____21356
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21356
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21361
                                                                  =
                                                                  let uu____21368
                                                                    =
                                                                    let uu____21369
                                                                    =
                                                                    let uu____21380
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21380) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21369 in
                                                                  (uu____21368,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21361 in
                                                              let uu____21401
                                                                =
                                                                let uu____21408
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21408
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21421
                                                                    =
                                                                    let uu____21424
                                                                    =
                                                                    let uu____21425
                                                                    =
                                                                    let uu____21432
                                                                    =
                                                                    let uu____21433
                                                                    =
                                                                    let uu____21444
                                                                    =
                                                                    let uu____21445
                                                                    =
                                                                    let uu____21450
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21450,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21445 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21444) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21433 in
                                                                    (uu____21432,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21425 in
                                                                    [uu____21424] in
                                                                    (d3,
                                                                    uu____21421) in
                                                              (match uu____21401
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21293
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
                            let uu____21515 =
                              let uu____21528 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21607  ->
                                   fun uu____21608  ->
                                     match (uu____21607, uu____21608) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21763 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21763 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21528 in
                            (match uu____21515 with
                             | (decls2,eqns,env01) ->
                                 let uu____21836 =
                                   let isDeclFun uu___91_21848 =
                                     match uu___91_21848 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21849 -> true
                                     | uu____21860 -> false in
                                   let uu____21861 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21861
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21836 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21901 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___92_21905  ->
                                 match uu___92_21905 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21906 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21912 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21912))) in
                      if uu____21901
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
                   let uu____21964 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21964
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
        let uu____22013 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22013 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22017 = encode_sigelt' env se in
      match uu____22017 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22033 =
                  let uu____22034 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22034 in
                [uu____22033]
            | uu____22035 ->
                let uu____22036 =
                  let uu____22039 =
                    let uu____22040 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22040 in
                  uu____22039 :: g in
                let uu____22041 =
                  let uu____22044 =
                    let uu____22045 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22045 in
                  [uu____22044] in
                FStar_List.append uu____22036 uu____22041 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22058 =
          let uu____22059 = FStar_Syntax_Subst.compress t in
          uu____22059.FStar_Syntax_Syntax.n in
        match uu____22058 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22063)) -> s = "opaque_to_smt"
        | uu____22064 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22069 =
          let uu____22070 = FStar_Syntax_Subst.compress t in
          uu____22070.FStar_Syntax_Syntax.n in
        match uu____22069 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22074)) -> s = "uninterpreted_by_smt"
        | uu____22075 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22080 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22085 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22088 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22091 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22106 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22110 =
            let uu____22111 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22111 Prims.op_Negation in
          if uu____22110
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22137 ->
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
               let uu____22157 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22157 with
               | (aname,atok,env2) ->
                   let uu____22173 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22173 with
                    | (formals,uu____22191) ->
                        let uu____22204 =
                          let uu____22209 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22209 env2 in
                        (match uu____22204 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22221 =
                                 let uu____22222 =
                                   let uu____22233 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22249  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22233,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22222 in
                               [uu____22221;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22262 =
                               let aux uu____22314 uu____22315 =
                                 match (uu____22314, uu____22315) with
                                 | ((bv,uu____22367),(env3,acc_sorts,acc)) ->
                                     let uu____22405 = gen_term_var env3 bv in
                                     (match uu____22405 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22262 with
                              | (uu____22477,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22500 =
                                      let uu____22507 =
                                        let uu____22508 =
                                          let uu____22519 =
                                            let uu____22520 =
                                              let uu____22525 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22525) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22520 in
                                          ([[app]], xs_sorts, uu____22519) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22508 in
                                      (uu____22507,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22500 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22545 =
                                      let uu____22552 =
                                        let uu____22553 =
                                          let uu____22564 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22564) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22553 in
                                      (uu____22552,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22545 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22583 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22583 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22611,uu____22612)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22613 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22613 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22630,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22636 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___93_22640  ->
                      match uu___93_22640 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22641 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22646 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22647 -> false)) in
            Prims.op_Negation uu____22636 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22656 =
               let uu____22663 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22663 env fv t quals in
             match uu____22656 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22678 =
                   let uu____22681 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22681 in
                 (uu____22678, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22689 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22689 with
           | (uu____22698,f1) ->
               let uu____22700 = encode_formula f1 env in
               (match uu____22700 with
                | (f2,decls) ->
                    let g =
                      let uu____22714 =
                        let uu____22715 =
                          let uu____22722 =
                            let uu____22725 =
                              let uu____22726 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22726 in
                            FStar_Pervasives_Native.Some uu____22725 in
                          let uu____22727 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22722, uu____22727) in
                        FStar_SMTEncoding_Util.mkAssume uu____22715 in
                      [uu____22714] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22733) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22745 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22763 =
                       let uu____22766 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22766.FStar_Syntax_Syntax.fv_name in
                     uu____22763.FStar_Syntax_Syntax.v in
                   let uu____22767 =
                     let uu____22768 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22768 in
                   if uu____22767
                   then
                     let val_decl =
                       let uu___128_22796 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___128_22796.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___128_22796.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___128_22796.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22801 = encode_sigelt' env1 val_decl in
                     match uu____22801 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22745 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22829,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22831;
                          FStar_Syntax_Syntax.lbtyp = uu____22832;
                          FStar_Syntax_Syntax.lbeff = uu____22833;
                          FStar_Syntax_Syntax.lbdef = uu____22834;_}::[]),uu____22835)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22854 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22854 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22883 =
                   let uu____22886 =
                     let uu____22887 =
                       let uu____22894 =
                         let uu____22895 =
                           let uu____22906 =
                             let uu____22907 =
                               let uu____22912 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22912) in
                             FStar_SMTEncoding_Util.mkEq uu____22907 in
                           ([[b2t_x]], [xx], uu____22906) in
                         FStar_SMTEncoding_Util.mkForall uu____22895 in
                       (uu____22894,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22887 in
                   [uu____22886] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22883 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22945,uu____22946) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___94_22955  ->
                  match uu___94_22955 with
                  | FStar_Syntax_Syntax.Discriminator uu____22956 -> true
                  | uu____22957 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22960,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22971 =
                     let uu____22972 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22972.FStar_Ident.idText in
                   uu____22971 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___95_22976  ->
                     match uu___95_22976 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22977 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22981) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___96_22998  ->
                  match uu___96_22998 with
                  | FStar_Syntax_Syntax.Projector uu____22999 -> true
                  | uu____23004 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23007 = try_lookup_free_var env l in
          (match uu____23007 with
           | FStar_Pervasives_Native.Some uu____23014 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___129_23018 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___129_23018.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___129_23018.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___129_23018.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23025) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23043) ->
          let uu____23052 = encode_sigelts env ses in
          (match uu____23052 with
           | (g,env1) ->
               let uu____23069 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___97_23092  ->
                         match uu___97_23092 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23093;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23094;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23095;_}
                             -> false
                         | uu____23098 -> true)) in
               (match uu____23069 with
                | (g',inversions) ->
                    let uu____23113 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___98_23134  ->
                              match uu___98_23134 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23135 ->
                                  true
                              | uu____23146 -> false)) in
                    (match uu____23113 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23164,tps,k,uu____23167,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___99_23184  ->
                    match uu___99_23184 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23185 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23194 = c in
              match uu____23194 with
              | (name,args,uu____23199,uu____23200,uu____23201) ->
                  let uu____23206 =
                    let uu____23207 =
                      let uu____23218 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23235  ->
                                match uu____23235 with
                                | (uu____23242,sort,uu____23244) -> sort)) in
                      (name, uu____23218, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23207 in
                  [uu____23206]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23271 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23277 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23277 FStar_Option.isNone)) in
            if uu____23271
            then []
            else
              (let uu____23309 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23309 with
               | (xxsym,xx) ->
                   let uu____23318 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23357  ->
                             fun l  ->
                               match uu____23357 with
                               | (out,decls) ->
                                   let uu____23377 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23377 with
                                    | (uu____23388,data_t) ->
                                        let uu____23390 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23390 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23436 =
                                                 let uu____23437 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23437.FStar_Syntax_Syntax.n in
                                               match uu____23436 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23448,indices) ->
                                                   indices
                                               | uu____23470 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23494  ->
                                                         match uu____23494
                                                         with
                                                         | (x,uu____23500) ->
                                                             let uu____23501
                                                               =
                                                               let uu____23502
                                                                 =
                                                                 let uu____23509
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23509,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23502 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23501)
                                                    env) in
                                             let uu____23512 =
                                               encode_args indices env1 in
                                             (match uu____23512 with
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
                                                      let uu____23538 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23554
                                                                 =
                                                                 let uu____23559
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23559,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23554)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23538
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23562 =
                                                      let uu____23563 =
                                                        let uu____23568 =
                                                          let uu____23569 =
                                                            let uu____23574 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23574,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23569 in
                                                        (out, uu____23568) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23563 in
                                                    (uu____23562,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23318 with
                    | (data_ax,decls) ->
                        let uu____23587 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23587 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23598 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23598 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23602 =
                                 let uu____23609 =
                                   let uu____23610 =
                                     let uu____23621 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23636 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23621,
                                       uu____23636) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23610 in
                                 let uu____23651 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23609,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23651) in
                               FStar_SMTEncoding_Util.mkAssume uu____23602 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23654 =
            let uu____23667 =
              let uu____23668 = FStar_Syntax_Subst.compress k in
              uu____23668.FStar_Syntax_Syntax.n in
            match uu____23667 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23713 -> (tps, k) in
          (match uu____23654 with
           | (formals,res) ->
               let uu____23736 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23736 with
                | (formals1,res1) ->
                    let uu____23747 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23747 with
                     | (vars,guards,env',binder_decls,uu____23772) ->
                         let uu____23785 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23785 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23804 =
                                  let uu____23811 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23811) in
                                FStar_SMTEncoding_Util.mkApp uu____23804 in
                              let uu____23820 =
                                let tname_decl =
                                  let uu____23830 =
                                    let uu____23831 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23863  ->
                                              match uu____23863 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23876 = varops.next_id () in
                                    (tname, uu____23831,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23876, false) in
                                  constructor_or_logic_type_decl uu____23830 in
                                let uu____23885 =
                                  match vars with
                                  | [] ->
                                      let uu____23898 =
                                        let uu____23899 =
                                          let uu____23902 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23902 in
                                        push_free_var env1 t tname
                                          uu____23899 in
                                      ([], uu____23898)
                                  | uu____23909 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23918 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23918 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23932 =
                                          let uu____23939 =
                                            let uu____23940 =
                                              let uu____23955 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23955) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23940 in
                                          (uu____23939,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23932 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23885 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23820 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23995 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23995 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24013 =
                                               let uu____24014 =
                                                 let uu____24021 =
                                                   let uu____24022 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24022 in
                                                 (uu____24021,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24014 in
                                             [uu____24013]
                                           else [] in
                                         let uu____24026 =
                                           let uu____24029 =
                                             let uu____24032 =
                                               let uu____24033 =
                                                 let uu____24040 =
                                                   let uu____24041 =
                                                     let uu____24052 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24052) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24041 in
                                                 (uu____24040,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24033 in
                                             [uu____24032] in
                                           FStar_List.append karr uu____24029 in
                                         FStar_List.append decls1 uu____24026 in
                                   let aux =
                                     let uu____24068 =
                                       let uu____24071 =
                                         inversion_axioms tapp vars in
                                       let uu____24074 =
                                         let uu____24077 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24077] in
                                       FStar_List.append uu____24071
                                         uu____24074 in
                                     FStar_List.append kindingAx uu____24068 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24084,uu____24085,uu____24086,uu____24087,uu____24088)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24096,t,uu____24098,n_tps,uu____24100) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24108 = new_term_constant_and_tok_from_lid env d in
          (match uu____24108 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24125 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24125 with
                | (formals,t_res) ->
                    let uu____24160 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24160 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24174 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24174 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24244 =
                                            mk_term_projector_name d x in
                                          (uu____24244,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24246 =
                                  let uu____24265 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24265, true) in
                                FStar_All.pipe_right uu____24246
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
                              let uu____24304 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24304 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24316::uu____24317 ->
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
                                         let uu____24362 =
                                           let uu____24373 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24373) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24362
                                     | uu____24398 -> tok_typing in
                                   let uu____24407 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24407 with
                                    | (vars',guards',env'',decls_formals,uu____24432)
                                        ->
                                        let uu____24445 =
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
                                        (match uu____24445 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24476 ->
                                                   let uu____24483 =
                                                     let uu____24484 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24484 in
                                                   [uu____24483] in
                                             let encode_elim uu____24494 =
                                               let uu____24495 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24495 with
                                               | (head1,args) ->
                                                   let uu____24538 =
                                                     let uu____24539 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24539.FStar_Syntax_Syntax.n in
                                                   (match uu____24538 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24549;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24550;_},uu____24551)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24557 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24557
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
                                                                 | uu____24600
                                                                    ->
                                                                    let uu____24601
                                                                    =
                                                                    let uu____24606
                                                                    =
                                                                    let uu____24607
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24607 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24606) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24601
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24623
                                                                    =
                                                                    let uu____24624
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24624 in
                                                                    if
                                                                    uu____24623
                                                                    then
                                                                    let uu____24637
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24637]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24639
                                                               =
                                                               let uu____24652
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24702
                                                                     ->
                                                                    fun
                                                                    uu____24703
                                                                     ->
                                                                    match 
                                                                    (uu____24702,
                                                                    uu____24703)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24798
                                                                    =
                                                                    let uu____24805
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24805 in
                                                                    (match uu____24798
                                                                    with
                                                                    | 
                                                                    (uu____24818,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24826
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24826
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24828
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24828
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
                                                                 uu____24652 in
                                                             (match uu____24639
                                                              with
                                                              | (uu____24843,arg_vars,elim_eqns_or_guards,uu____24846)
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
                                                                    let uu____24876
                                                                    =
                                                                    let uu____24883
                                                                    =
                                                                    let uu____24884
                                                                    =
                                                                    let uu____24895
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24906
                                                                    =
                                                                    let uu____24907
                                                                    =
                                                                    let uu____24912
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24912) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24907 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24895,
                                                                    uu____24906) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24884 in
                                                                    (uu____24883,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24876 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24935
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24935,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24937
                                                                    =
                                                                    let uu____24944
                                                                    =
                                                                    let uu____24945
                                                                    =
                                                                    let uu____24956
                                                                    =
                                                                    let uu____24961
                                                                    =
                                                                    let uu____24964
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24964] in
                                                                    [uu____24961] in
                                                                    let uu____24969
                                                                    =
                                                                    let uu____24970
                                                                    =
                                                                    let uu____24975
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24976
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24975,
                                                                    uu____24976) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24970 in
                                                                    (uu____24956,
                                                                    [x],
                                                                    uu____24969) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24945 in
                                                                    let uu____24995
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24944,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24995) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24937
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25002
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
                                                                    (let uu____25030
                                                                    =
                                                                    let uu____25031
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25031
                                                                    dapp1 in
                                                                    [uu____25030]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25002
                                                                    FStar_List.flatten in
                                                                    let uu____25038
                                                                    =
                                                                    let uu____25045
                                                                    =
                                                                    let uu____25046
                                                                    =
                                                                    let uu____25057
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25068
                                                                    =
                                                                    let uu____25069
                                                                    =
                                                                    let uu____25074
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25074) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25069 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25057,
                                                                    uu____25068) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25046 in
                                                                    (uu____25045,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25038) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25095 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25095
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
                                                                 | uu____25138
                                                                    ->
                                                                    let uu____25139
                                                                    =
                                                                    let uu____25144
                                                                    =
                                                                    let uu____25145
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25145 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25144) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25139
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25161
                                                                    =
                                                                    let uu____25162
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25162 in
                                                                    if
                                                                    uu____25161
                                                                    then
                                                                    let uu____25175
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25175]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25177
                                                               =
                                                               let uu____25190
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25240
                                                                     ->
                                                                    fun
                                                                    uu____25241
                                                                     ->
                                                                    match 
                                                                    (uu____25240,
                                                                    uu____25241)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25336
                                                                    =
                                                                    let uu____25343
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25343 in
                                                                    (match uu____25336
                                                                    with
                                                                    | 
                                                                    (uu____25356,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25364
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25364
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25366
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25366
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
                                                                 uu____25190 in
                                                             (match uu____25177
                                                              with
                                                              | (uu____25381,arg_vars,elim_eqns_or_guards,uu____25384)
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
                                                                    let uu____25414
                                                                    =
                                                                    let uu____25421
                                                                    =
                                                                    let uu____25422
                                                                    =
                                                                    let uu____25433
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25444
                                                                    =
                                                                    let uu____25445
                                                                    =
                                                                    let uu____25450
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25450) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25445 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25433,
                                                                    uu____25444) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25422 in
                                                                    (uu____25421,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25414 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25473
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25473,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25475
                                                                    =
                                                                    let uu____25482
                                                                    =
                                                                    let uu____25483
                                                                    =
                                                                    let uu____25494
                                                                    =
                                                                    let uu____25499
                                                                    =
                                                                    let uu____25502
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25502] in
                                                                    [uu____25499] in
                                                                    let uu____25507
                                                                    =
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25513
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25514
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25513,
                                                                    uu____25514) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25508 in
                                                                    (uu____25494,
                                                                    [x],
                                                                    uu____25507) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25483 in
                                                                    let uu____25533
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25482,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25533) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25475
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25540
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
                                                                    (let uu____25568
                                                                    =
                                                                    let uu____25569
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25569
                                                                    dapp1 in
                                                                    [uu____25568]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25540
                                                                    FStar_List.flatten in
                                                                    let uu____25576
                                                                    =
                                                                    let uu____25583
                                                                    =
                                                                    let uu____25584
                                                                    =
                                                                    let uu____25595
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25606
                                                                    =
                                                                    let uu____25607
                                                                    =
                                                                    let uu____25612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25612) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25607 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25595,
                                                                    uu____25606) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25584 in
                                                                    (uu____25583,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25576) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25631 ->
                                                        ((let uu____25633 =
                                                            let uu____25638 =
                                                              let uu____25639
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25640
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25639
                                                                uu____25640 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25638) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25633);
                                                         ([], []))) in
                                             let uu____25645 = encode_elim () in
                                             (match uu____25645 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25665 =
                                                      let uu____25668 =
                                                        let uu____25671 =
                                                          let uu____25674 =
                                                            let uu____25677 =
                                                              let uu____25678
                                                                =
                                                                let uu____25689
                                                                  =
                                                                  let uu____25692
                                                                    =
                                                                    let uu____25693
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25693 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25692 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25689) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25678 in
                                                            [uu____25677] in
                                                          let uu____25698 =
                                                            let uu____25701 =
                                                              let uu____25704
                                                                =
                                                                let uu____25707
                                                                  =
                                                                  let uu____25710
                                                                    =
                                                                    let uu____25713
                                                                    =
                                                                    let uu____25716
                                                                    =
                                                                    let uu____25717
                                                                    =
                                                                    let uu____25724
                                                                    =
                                                                    let uu____25725
                                                                    =
                                                                    let uu____25736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25736) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25725 in
                                                                    (uu____25724,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25717 in
                                                                    let uu____25749
                                                                    =
                                                                    let uu____25752
                                                                    =
                                                                    let uu____25753
                                                                    =
                                                                    let uu____25760
                                                                    =
                                                                    let uu____25761
                                                                    =
                                                                    let uu____25772
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25783
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25772,
                                                                    uu____25783) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25761 in
                                                                    (uu____25760,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25753 in
                                                                    [uu____25752] in
                                                                    uu____25716
                                                                    ::
                                                                    uu____25749 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25713 in
                                                                  FStar_List.append
                                                                    uu____25710
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25707 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25704 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25701 in
                                                          FStar_List.append
                                                            uu____25674
                                                            uu____25698 in
                                                        FStar_List.append
                                                          decls3 uu____25671 in
                                                      FStar_List.append
                                                        decls2 uu____25668 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25665 in
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
           (fun uu____25829  ->
              fun se  ->
                match uu____25829 with
                | (g,env1) ->
                    let uu____25849 = encode_sigelt env1 se in
                    (match uu____25849 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25906 =
        match uu____25906 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25938 ->
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
                 ((let uu____25944 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25944
                   then
                     let uu____25945 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25946 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25947 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25945 uu____25946 uu____25947
                   else ());
                  (let uu____25949 = encode_term t1 env1 in
                   match uu____25949 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25965 =
                         let uu____25972 =
                           let uu____25973 =
                             let uu____25974 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25974
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25973 in
                         new_term_constant_from_string env1 x uu____25972 in
                       (match uu____25965 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25990 = FStar_Options.log_queries () in
                              if uu____25990
                              then
                                let uu____25993 =
                                  let uu____25994 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25995 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25996 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25994 uu____25995 uu____25996 in
                                FStar_Pervasives_Native.Some uu____25993
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26012,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26026 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26026 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26049,se,uu____26051) ->
                 let uu____26056 = encode_sigelt env1 se in
                 (match uu____26056 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26073,se) ->
                 let uu____26079 = encode_sigelt env1 se in
                 (match uu____26079 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26096 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26096 with | (uu____26119,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26131 'Auu____26132 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26132,'Auu____26131)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26200  ->
              match uu____26200 with
              | (l,uu____26212,uu____26213) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26259  ->
              match uu____26259 with
              | (l,uu____26273,uu____26274) ->
                  let uu____26283 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26284 =
                    let uu____26287 =
                      let uu____26288 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26288 in
                    [uu____26287] in
                  uu____26283 :: uu____26284)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26313 =
      let uu____26316 =
        let uu____26317 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26320 =
          let uu____26321 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26321 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26317;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26320
        } in
      [uu____26316] in
    FStar_ST.op_Colon_Equals last_env uu____26313
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26351 = FStar_ST.op_Bang last_env in
      match uu____26351 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26378 ->
          let uu___130_26381 = e in
          let uu____26382 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___130_26381.bindings);
            depth = (uu___130_26381.depth);
            tcenv;
            warn = (uu___130_26381.warn);
            cache = (uu___130_26381.cache);
            nolabels = (uu___130_26381.nolabels);
            use_zfuel_name = (uu___130_26381.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___130_26381.encode_non_total_function_typ);
            current_module_name = uu____26382
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26386 = FStar_ST.op_Bang last_env in
    match uu____26386 with
    | [] -> failwith "Empty env stack"
    | uu____26412::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26441  ->
    let uu____26442 = FStar_ST.op_Bang last_env in
    match uu____26442 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___131_26476 = hd1 in
          {
            bindings = (uu___131_26476.bindings);
            depth = (uu___131_26476.depth);
            tcenv = (uu___131_26476.tcenv);
            warn = (uu___131_26476.warn);
            cache = refs;
            nolabels = (uu___131_26476.nolabels);
            use_zfuel_name = (uu___131_26476.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_26476.encode_non_total_function_typ);
            current_module_name = (uu___131_26476.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26502  ->
    let uu____26503 = FStar_ST.op_Bang last_env in
    match uu____26503 with
    | [] -> failwith "Popping an empty stack"
    | uu____26529::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26593::uu____26594,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___132_26602 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___132_26602.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___132_26602.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___132_26602.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26603 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26618 =
        let uu____26621 =
          let uu____26622 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26622 in
        let uu____26623 = open_fact_db_tags env in uu____26621 :: uu____26623 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26618
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
      let uu____26645 = encode_sigelt env se in
      match uu____26645 with
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
        let uu____26681 = FStar_Options.log_queries () in
        if uu____26681
        then
          let uu____26684 =
            let uu____26685 =
              let uu____26686 =
                let uu____26687 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26687 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26686 in
            FStar_SMTEncoding_Term.Caption uu____26685 in
          uu____26684 :: decls
        else decls in
      (let uu____26698 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26698
       then
         let uu____26699 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26699
       else ());
      (let env =
         let uu____26702 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26702 tcenv in
       let uu____26703 = encode_top_level_facts env se in
       match uu____26703 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26717 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26717)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26729 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26729
       then
         let uu____26730 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26730
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26765  ->
                 fun se  ->
                   match uu____26765 with
                   | (g,env2) ->
                       let uu____26785 = encode_top_level_facts env2 se in
                       (match uu____26785 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26808 =
         encode_signature
           (let uu___133_26817 = env in
            {
              bindings = (uu___133_26817.bindings);
              depth = (uu___133_26817.depth);
              tcenv = (uu___133_26817.tcenv);
              warn = false;
              cache = (uu___133_26817.cache);
              nolabels = (uu___133_26817.nolabels);
              use_zfuel_name = (uu___133_26817.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_26817.encode_non_total_function_typ);
              current_module_name = (uu___133_26817.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26808 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26834 = FStar_Options.log_queries () in
             if uu____26834
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___134_26842 = env1 in
               {
                 bindings = (uu___134_26842.bindings);
                 depth = (uu___134_26842.depth);
                 tcenv = (uu___134_26842.tcenv);
                 warn = true;
                 cache = (uu___134_26842.cache);
                 nolabels = (uu___134_26842.nolabels);
                 use_zfuel_name = (uu___134_26842.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___134_26842.encode_non_total_function_typ);
                 current_module_name = (uu___134_26842.current_module_name)
               });
            (let uu____26844 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26844
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
        (let uu____26896 =
           let uu____26897 = FStar_TypeChecker_Env.current_module tcenv in
           uu____26897.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26896);
        (let env =
           let uu____26899 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____26899 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____26911 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26946 = aux rest in
                 (match uu____26946 with
                  | (out,rest1) ->
                      let t =
                        let uu____26976 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____26976 with
                        | FStar_Pervasives_Native.Some uu____26981 ->
                            let uu____26982 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____26982
                              x.FStar_Syntax_Syntax.sort
                        | uu____26983 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____26987 =
                        let uu____26990 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___135_26993 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___135_26993.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___135_26993.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____26990 :: out in
                      (uu____26987, rest1))
             | uu____26998 -> ([], bindings1) in
           let uu____27005 = aux bindings in
           match uu____27005 with
           | (closing,bindings1) ->
               let uu____27030 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27030, bindings1) in
         match uu____26911 with
         | (q1,bindings1) ->
             let uu____27053 =
               let uu____27058 =
                 FStar_List.filter
                   (fun uu___100_27063  ->
                      match uu___100_27063 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27064 ->
                          false
                      | uu____27071 -> true) bindings1 in
               encode_env_bindings env uu____27058 in
             (match uu____27053 with
              | (env_decls,env1) ->
                  ((let uu____27089 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27089
                    then
                      let uu____27090 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27090
                    else ());
                   (let uu____27092 = encode_formula q1 env1 in
                    match uu____27092 with
                    | (phi,qdecls) ->
                        let uu____27113 =
                          let uu____27118 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27118 phi in
                        (match uu____27113 with
                         | (labels,phi1) ->
                             let uu____27135 = encode_labels labels in
                             (match uu____27135 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27172 =
                                      let uu____27179 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27180 =
                                        varops.mk_unique "@query" in
                                      (uu____27179,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27180) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27172 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))