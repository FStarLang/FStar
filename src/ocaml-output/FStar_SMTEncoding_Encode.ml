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
      (fun uu___79_107  ->
         match uu___79_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___102_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___102_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___102_143.FStar_Syntax_Syntax.sort)
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
    let uu___103_1621 = x in
    let uu____1622 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1622;
      FStar_Syntax_Syntax.index = (uu___103_1621.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___103_1621.FStar_Syntax_Syntax.sort)
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
                 (fun uu___80_2069  ->
                    match uu___80_2069 with
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
           (fun uu___81_2092  ->
              match uu___81_2092 with
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
        (let uu___104_2172 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___104_2172.tcenv);
           warn = (uu___104_2172.warn);
           cache = (uu___104_2172.cache);
           nolabels = (uu___104_2172.nolabels);
           use_zfuel_name = (uu___104_2172.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___104_2172.encode_non_total_function_typ);
           current_module_name = (uu___104_2172.current_module_name)
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
        (let uu___105_2190 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___105_2190.depth);
           tcenv = (uu___105_2190.tcenv);
           warn = (uu___105_2190.warn);
           cache = (uu___105_2190.cache);
           nolabels = (uu___105_2190.nolabels);
           use_zfuel_name = (uu___105_2190.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___105_2190.encode_non_total_function_typ);
           current_module_name = (uu___105_2190.current_module_name)
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
          (let uu___106_2211 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___106_2211.depth);
             tcenv = (uu___106_2211.tcenv);
             warn = (uu___106_2211.warn);
             cache = (uu___106_2211.cache);
             nolabels = (uu___106_2211.nolabels);
             use_zfuel_name = (uu___106_2211.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___106_2211.encode_non_total_function_typ);
             current_module_name = (uu___106_2211.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___107_2221 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___107_2221.depth);
          tcenv = (uu___107_2221.tcenv);
          warn = (uu___107_2221.warn);
          cache = (uu___107_2221.cache);
          nolabels = (uu___107_2221.nolabels);
          use_zfuel_name = (uu___107_2221.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___107_2221.encode_non_total_function_typ);
          current_module_name = (uu___107_2221.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___82_2245  ->
             match uu___82_2245 with
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
        let uu___108_2316 = env in
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
          depth = (uu___108_2316.depth);
          tcenv = (uu___108_2316.tcenv);
          warn = (uu___108_2316.warn);
          cache = (uu___108_2316.cache);
          nolabels = (uu___108_2316.nolabels);
          use_zfuel_name = (uu___108_2316.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___108_2316.encode_non_total_function_typ);
          current_module_name = (uu___108_2316.current_module_name)
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
        (fun uu___83_2379  ->
           match uu___83_2379 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2418 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2435 =
        lookup_binding env
          (fun uu___84_2443  ->
             match uu___84_2443 with
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
          let uu___109_2559 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___109_2559.depth);
            tcenv = (uu___109_2559.tcenv);
            warn = (uu___109_2559.warn);
            cache = (uu___109_2559.cache);
            nolabels = (uu___109_2559.nolabels);
            use_zfuel_name = (uu___109_2559.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___109_2559.encode_non_total_function_typ);
            current_module_name = (uu___109_2559.current_module_name)
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
            let uu___110_2611 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___110_2611.depth);
              tcenv = (uu___110_2611.tcenv);
              warn = (uu___110_2611.warn);
              cache = (uu___110_2611.cache);
              nolabels = (uu___110_2611.nolabels);
              use_zfuel_name = (uu___110_2611.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___110_2611.encode_non_total_function_typ);
              current_module_name = (uu___110_2611.current_module_name)
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
        (fun uu___85_2855  ->
           match uu___85_2855 with
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
               (fun uu___86_3174  ->
                  match uu___86_3174 with
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
  fun uu___87_3272  ->
    match uu___87_3272 with
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
                (fun a415  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a415)
                (fun a416  -> (Obj.magic binary) a416) in
            let sub1 =
              mk_l ()
                (fun a417  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a417)
                (fun a418  -> (Obj.magic binary) a418) in
            let minus =
              mk_l ()
                (fun a419  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a419)
                (fun a420  -> (Obj.magic unary) a420) in
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
                          (fun a421  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a421)
                          (fun a422  -> (Obj.magic binary) a422)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv ()
                          (fun a423  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a423)
                          (fun a424  -> (Obj.magic binary) a424)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv ()
                          (fun a425  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a425)
                          (fun a426  -> (Obj.magic binary) a426)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv ()
                          (fun a427  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a427)
                          (fun a428  -> (Obj.magic binary) a428)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv ()
                          (fun a429  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a429)
                          (fun a430  -> (Obj.magic binary) a430)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv ()
                          (fun a431  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a431)
                          (fun a432  -> (Obj.magic binary_arith) a432)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv ()
                          (fun a433  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a433)
                          (fun a434  -> (Obj.magic binary_arith) a434)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv ()
                          (fun a435  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a435)
                          (fun a436  -> (Obj.magic binary_arith) a436)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv ()
                          (fun a437  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a437)
                          (fun a438  -> (Obj.magic binary_arith) a438)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv ()
                          (fun a439  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a439)
                          (fun a440  -> (Obj.magic binary_arith) a440)
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv ()
                          (fun a441  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a441)
                          (fun a442  -> (Obj.magic binary) a442)
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
                        mk_bv () (fun a443  -> (Obj.magic uu____5373) a443)
                          (fun a444  -> (Obj.magic unary) a444) uu____5378
                          arg_tms2 in
                      let to_int1 =
                        mk_bv ()
                          (fun a445  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a445) (fun a446  -> (Obj.magic unary) a446)
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv ()
                          (fun a447  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a447)
                          (fun a448  -> (Obj.magic unary_arith) a448)
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
                           (let uu___111_5942 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___111_5942.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___111_5942.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___111_5942.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___111_5942.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___111_5942.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___111_5942.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___111_5942.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___111_5942.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___111_5942.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___111_5942.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___111_5942.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___111_5942.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___111_5942.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___111_5942.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___111_5942.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___111_5942.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___111_5942.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___111_5942.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___111_5942.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___111_5942.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___111_5942.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___111_5942.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___111_5942.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___111_5942.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___111_5942.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___111_5942.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___111_5942.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___111_5942.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___111_5942.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___111_5942.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___111_5942.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___111_5942.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___111_5942.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___111_5942.FStar_TypeChecker_Env.dep_graph)
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
                          FStar_Syntax_Syntax.lbdef = uu____8295;
                          FStar_Syntax_Syntax.lbattrs = uu____8296;_}::uu____8297),uu____8298)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8328;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8330;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8332;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8356 ->
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
              let uu____8426 = encode_term e1 env in
              match uu____8426 with
              | (ee1,decls1) ->
                  let uu____8437 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8437 with
                   | (xs,e21) ->
                       let uu____8462 = FStar_List.hd xs in
                       (match uu____8462 with
                        | (x1,uu____8476) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8478 = encode_body e21 env' in
                            (match uu____8478 with
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
            let uu____8510 =
              let uu____8517 =
                let uu____8518 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8518 in
              gen_term_var env uu____8517 in
            match uu____8510 with
            | (scrsym,scr',env1) ->
                let uu____8526 = encode_term e env1 in
                (match uu____8526 with
                 | (scr,decls) ->
                     let uu____8537 =
                       let encode_branch b uu____8562 =
                         match uu____8562 with
                         | (else_case,decls1) ->
                             let uu____8581 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8581 with
                              | (p,w,br) ->
                                  let uu____8607 = encode_pat env1 p in
                                  (match uu____8607 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8644  ->
                                                   match uu____8644 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8651 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8673 =
                                               encode_term w1 env2 in
                                             (match uu____8673 with
                                              | (w2,decls2) ->
                                                  let uu____8686 =
                                                    let uu____8687 =
                                                      let uu____8692 =
                                                        let uu____8693 =
                                                          let uu____8698 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8698) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8693 in
                                                      (guard, uu____8692) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8687 in
                                                  (uu____8686, decls2)) in
                                       (match uu____8651 with
                                        | (guard1,decls2) ->
                                            let uu____8711 =
                                              encode_br br env2 in
                                            (match uu____8711 with
                                             | (br1,decls3) ->
                                                 let uu____8724 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8724,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8537 with
                      | (match_tm,decls1) ->
                          let uu____8743 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____8743, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____8783 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____8783
       then
         let uu____8784 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8784
       else ());
      (let uu____8786 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____8786 with
       | (vars,pat_term) ->
           let uu____8803 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8856  ->
                     fun v1  ->
                       match uu____8856 with
                       | (env1,vars1) ->
                           let uu____8908 = gen_term_var env1 v1 in
                           (match uu____8908 with
                            | (xx,uu____8930,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____8803 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9009 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9010 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9011 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9019 = encode_const c env1 in
                      (match uu____9019 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9033::uu____9034 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9037 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9060 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9060 with
                        | (uu____9067,uu____9068::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9071 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9104  ->
                                  match uu____9104 with
                                  | (arg,uu____9112) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9118 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9118)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9145) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9176 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9199 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9243  ->
                                  match uu____9243 with
                                  | (arg,uu____9257) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9263 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9263)) in
                      FStar_All.pipe_right uu____9199 FStar_List.flatten in
                let pat_term1 uu____9291 = encode_term pat_term env1 in
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
      let uu____9301 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9339  ->
                fun uu____9340  ->
                  match (uu____9339, uu____9340) with
                  | ((tms,decls),(t,uu____9376)) ->
                      let uu____9397 = encode_term t env in
                      (match uu____9397 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9301 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9454 = FStar_Syntax_Util.list_elements e in
        match uu____9454 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9475 =
          let uu____9490 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9490 FStar_Syntax_Util.head_and_args in
        match uu____9475 with
        | (head1,args) ->
            let uu____9529 =
              let uu____9542 =
                let uu____9543 = FStar_Syntax_Util.un_uinst head1 in
                uu____9543.FStar_Syntax_Syntax.n in
              (uu____9542, args) in
            (match uu____9529 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9557,uu____9558)::(e,uu____9560)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9595 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9631 =
            let uu____9646 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9646 FStar_Syntax_Util.head_and_args in
          match uu____9631 with
          | (head1,args) ->
              let uu____9687 =
                let uu____9700 =
                  let uu____9701 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9701.FStar_Syntax_Syntax.n in
                (uu____9700, args) in
              (match uu____9687 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9718)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9745 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____9767 = smt_pat_or1 t1 in
            (match uu____9767 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9783 = list_elements1 e in
                 FStar_All.pipe_right uu____9783
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9801 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____9801
                           (FStar_List.map one_pat)))
             | uu____9812 ->
                 let uu____9817 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____9817])
        | uu____9838 ->
            let uu____9841 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____9841] in
      let uu____9862 =
        let uu____9881 =
          let uu____9882 = FStar_Syntax_Subst.compress t in
          uu____9882.FStar_Syntax_Syntax.n in
        match uu____9881 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9921 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____9921 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9964;
                        FStar_Syntax_Syntax.effect_name = uu____9965;
                        FStar_Syntax_Syntax.result_typ = uu____9966;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9968)::(post,uu____9970)::(pats,uu____9972)::[];
                        FStar_Syntax_Syntax.flags = uu____9973;_}
                      ->
                      let uu____10014 = lemma_pats pats in
                      (binders1, pre, post, uu____10014)
                  | uu____10031 -> failwith "impos"))
        | uu____10050 -> failwith "Impos" in
      match uu____9862 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___112_10098 = env in
            {
              bindings = (uu___112_10098.bindings);
              depth = (uu___112_10098.depth);
              tcenv = (uu___112_10098.tcenv);
              warn = (uu___112_10098.warn);
              cache = (uu___112_10098.cache);
              nolabels = (uu___112_10098.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___112_10098.encode_non_total_function_typ);
              current_module_name = (uu___112_10098.current_module_name)
            } in
          let uu____10099 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10099 with
           | (vars,guards,env2,decls,uu____10124) ->
               let uu____10137 =
                 let uu____10152 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10206 =
                             let uu____10217 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2)) in
                             FStar_All.pipe_right uu____10217
                               FStar_List.unzip in
                           match uu____10206 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10152 FStar_List.unzip in
               (match uu____10137 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___113_10369 = env2 in
                      {
                        bindings = (uu___113_10369.bindings);
                        depth = (uu___113_10369.depth);
                        tcenv = (uu___113_10369.tcenv);
                        warn = (uu___113_10369.warn);
                        cache = (uu___113_10369.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___113_10369.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___113_10369.encode_non_total_function_typ);
                        current_module_name =
                          (uu___113_10369.current_module_name)
                      } in
                    let uu____10370 =
                      let uu____10375 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10375 env3 in
                    (match uu____10370 with
                     | (pre1,decls'') ->
                         let uu____10382 =
                           let uu____10387 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10387 env3 in
                         (match uu____10382 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10397 =
                                let uu____10398 =
                                  let uu____10409 =
                                    let uu____10410 =
                                      let uu____10415 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10415, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10410 in
                                  (pats, vars, uu____10409) in
                                FStar_SMTEncoding_Util.mkForall uu____10398 in
                              (uu____10397, decls1)))))
and encode_smt_pattern:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let uu____10428 = FStar_Syntax_Util.head_and_args t in
      match uu____10428 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1 in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10487::(x,uu____10489)::(t1,uu____10491)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10538 = encode_term x env in
               (match uu____10538 with
                | (x1,decls) ->
                    let uu____10551 = encode_term t1 env in
                    (match uu____10551 with
                     | (t2,decls') ->
                         let uu____10564 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                         (uu____10564, (FStar_List.append decls decls'))))
           | uu____10567 -> encode_term t env)
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10590 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10590
        then
          let uu____10591 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10592 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10591 uu____10592
        else () in
      let enc f r l =
        let uu____10625 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10653 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10653 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10625 with
        | (decls,args) ->
            let uu____10682 =
              let uu___114_10683 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10683.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10683.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10682, decls) in
      let const_op f r uu____10714 =
        let uu____10727 = f r in (uu____10727, []) in
      let un_op f l =
        let uu____10746 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10746 in
      let bin_op f uu___88_10762 =
        match uu___88_10762 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10773 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10807 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10830  ->
                 match uu____10830 with
                 | (t,uu____10844) ->
                     let uu____10845 = encode_formula t env in
                     (match uu____10845 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10807 with
        | (decls,phis) ->
            let uu____10874 =
              let uu___115_10875 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___115_10875.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___115_10875.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10874, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10936  ->
               match uu____10936 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10955) -> false
                    | uu____10956 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10971 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____10971
        else
          (let uu____10985 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____10985 r rf) in
      let mk_imp1 r uu___89_11010 =
        match uu___89_11010 with
        | (lhs,uu____11016)::(rhs,uu____11018)::[] ->
            let uu____11045 = encode_formula rhs env in
            (match uu____11045 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11060) ->
                      (l1, decls1)
                  | uu____11065 ->
                      let uu____11066 = encode_formula lhs env in
                      (match uu____11066 with
                       | (l2,decls2) ->
                           let uu____11077 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11077, (FStar_List.append decls1 decls2)))))
        | uu____11080 -> failwith "impossible" in
      let mk_ite r uu___90_11101 =
        match uu___90_11101 with
        | (guard,uu____11107)::(_then,uu____11109)::(_else,uu____11111)::[]
            ->
            let uu____11148 = encode_formula guard env in
            (match uu____11148 with
             | (g,decls1) ->
                 let uu____11159 = encode_formula _then env in
                 (match uu____11159 with
                  | (t,decls2) ->
                      let uu____11170 = encode_formula _else env in
                      (match uu____11170 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11184 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11209 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11209 in
      let connectives =
        let uu____11227 =
          let uu____11240 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11240) in
        let uu____11257 =
          let uu____11272 =
            let uu____11285 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11285) in
          let uu____11302 =
            let uu____11317 =
              let uu____11332 =
                let uu____11345 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11345) in
              let uu____11362 =
                let uu____11377 =
                  let uu____11392 =
                    let uu____11405 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11405) in
                  [uu____11392;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11377 in
              uu____11332 :: uu____11362 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11317 in
          uu____11272 :: uu____11302 in
        uu____11227 :: uu____11257 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11726 = encode_formula phi' env in
            (match uu____11726 with
             | (phi2,decls) ->
                 let uu____11737 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11737, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11738 ->
            let uu____11745 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11745 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11784 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11784 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11796;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11798;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11800;_}::[]),e2)
            ->
            let uu____11824 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11824 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11871::(x,uu____11873)::(t,uu____11875)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11922 = encode_term x env in
                 (match uu____11922 with
                  | (x1,decls) ->
                      let uu____11933 = encode_term t env in
                      (match uu____11933 with
                       | (t1,decls') ->
                           let uu____11944 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11944, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11949)::(msg,uu____11951)::(phi2,uu____11953)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11998 =
                   let uu____12003 =
                     let uu____12004 = FStar_Syntax_Subst.compress r in
                     uu____12004.FStar_Syntax_Syntax.n in
                   let uu____12007 =
                     let uu____12008 = FStar_Syntax_Subst.compress msg in
                     uu____12008.FStar_Syntax_Syntax.n in
                   (uu____12003, uu____12007) in
                 (match uu____11998 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12017))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12023 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12030)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12055 when head_redex env head2 ->
                 let uu____12068 = whnf env phi1 in
                 encode_formula uu____12068 env
             | uu____12069 ->
                 let uu____12082 = encode_term phi1 env in
                 (match uu____12082 with
                  | (tt,decls) ->
                      let uu____12093 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___116_12096 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___116_12096.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___116_12096.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12093, decls)))
        | uu____12097 ->
            let uu____12098 = encode_term phi1 env in
            (match uu____12098 with
             | (tt,decls) ->
                 let uu____12109 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___117_12112 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___117_12112.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___117_12112.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12109, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12148 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12148 with
        | (vars,guards,env2,decls,uu____12187) ->
            let uu____12200 =
              let uu____12213 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12265 =
                          let uu____12276 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12316  ->
                                    match uu____12316 with
                                    | (t,uu____12330) ->
                                        encode_smt_pattern t
                                          (let uu___118_12336 = env2 in
                                           {
                                             bindings =
                                               (uu___118_12336.bindings);
                                             depth = (uu___118_12336.depth);
                                             tcenv = (uu___118_12336.tcenv);
                                             warn = (uu___118_12336.warn);
                                             cache = (uu___118_12336.cache);
                                             nolabels =
                                               (uu___118_12336.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___118_12336.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___118_12336.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12276 FStar_List.unzip in
                        match uu____12265 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12213 FStar_List.unzip in
            (match uu____12200 with
             | (pats,decls') ->
                 let uu____12445 = encode_formula body env2 in
                 (match uu____12445 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12477;
                             FStar_SMTEncoding_Term.rng = uu____12478;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12493 -> guards in
                      let uu____12498 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12498, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12558  ->
                   match uu____12558 with
                   | (x,uu____12564) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12572 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12584 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12584) uu____12572 tl1 in
             let uu____12587 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12614  ->
                       match uu____12614 with
                       | (b,uu____12620) ->
                           let uu____12621 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12621)) in
             (match uu____12587 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12627) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12641 =
                    let uu____12646 =
                      let uu____12647 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12647 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12646) in
                  FStar_Errors.log_issue pos uu____12641) in
       let uu____12648 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12648 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12657 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12715  ->
                     match uu____12715 with
                     | (l,uu____12729) -> FStar_Ident.lid_equals op l)) in
           (match uu____12657 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12762,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12802 = encode_q_body env vars pats body in
             match uu____12802 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12847 =
                     let uu____12858 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12858) in
                   FStar_SMTEncoding_Term.mkForall uu____12847
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12877 = encode_q_body env vars pats body in
             match uu____12877 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12921 =
                   let uu____12922 =
                     let uu____12933 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12933) in
                   FStar_SMTEncoding_Term.mkExists uu____12922
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12921, decls))))
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
  let uu____13026 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13026 with
  | (asym,a) ->
      let uu____13033 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13033 with
       | (xsym,x) ->
           let uu____13040 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13040 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13084 =
                      let uu____13095 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13095, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13084 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13121 =
                      let uu____13128 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13128) in
                    FStar_SMTEncoding_Util.mkApp uu____13121 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13141 =
                    let uu____13144 =
                      let uu____13147 =
                        let uu____13150 =
                          let uu____13151 =
                            let uu____13158 =
                              let uu____13159 =
                                let uu____13170 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13170) in
                              FStar_SMTEncoding_Util.mkForall uu____13159 in
                            (uu____13158, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13151 in
                        let uu____13187 =
                          let uu____13190 =
                            let uu____13191 =
                              let uu____13198 =
                                let uu____13199 =
                                  let uu____13210 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13210) in
                                FStar_SMTEncoding_Util.mkForall uu____13199 in
                              (uu____13198,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13191 in
                          [uu____13190] in
                        uu____13150 :: uu____13187 in
                      xtok_decl :: uu____13147 in
                    xname_decl :: uu____13144 in
                  (xtok1, uu____13141) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13301 =
                    let uu____13314 =
                      let uu____13323 =
                        let uu____13324 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13324 in
                      quant axy uu____13323 in
                    (FStar_Parser_Const.op_Eq, uu____13314) in
                  let uu____13333 =
                    let uu____13348 =
                      let uu____13361 =
                        let uu____13370 =
                          let uu____13371 =
                            let uu____13372 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13372 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13371 in
                        quant axy uu____13370 in
                      (FStar_Parser_Const.op_notEq, uu____13361) in
                    let uu____13381 =
                      let uu____13396 =
                        let uu____13409 =
                          let uu____13418 =
                            let uu____13419 =
                              let uu____13420 =
                                let uu____13425 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13426 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13425, uu____13426) in
                              FStar_SMTEncoding_Util.mkLT uu____13420 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13419 in
                          quant xy uu____13418 in
                        (FStar_Parser_Const.op_LT, uu____13409) in
                      let uu____13435 =
                        let uu____13450 =
                          let uu____13463 =
                            let uu____13472 =
                              let uu____13473 =
                                let uu____13474 =
                                  let uu____13479 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13480 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13479, uu____13480) in
                                FStar_SMTEncoding_Util.mkLTE uu____13474 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13473 in
                            quant xy uu____13472 in
                          (FStar_Parser_Const.op_LTE, uu____13463) in
                        let uu____13489 =
                          let uu____13504 =
                            let uu____13517 =
                              let uu____13526 =
                                let uu____13527 =
                                  let uu____13528 =
                                    let uu____13533 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13534 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13533, uu____13534) in
                                  FStar_SMTEncoding_Util.mkGT uu____13528 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13527 in
                              quant xy uu____13526 in
                            (FStar_Parser_Const.op_GT, uu____13517) in
                          let uu____13543 =
                            let uu____13558 =
                              let uu____13571 =
                                let uu____13580 =
                                  let uu____13581 =
                                    let uu____13582 =
                                      let uu____13587 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13588 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13587, uu____13588) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13582 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13581 in
                                quant xy uu____13580 in
                              (FStar_Parser_Const.op_GTE, uu____13571) in
                            let uu____13597 =
                              let uu____13612 =
                                let uu____13625 =
                                  let uu____13634 =
                                    let uu____13635 =
                                      let uu____13636 =
                                        let uu____13641 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13642 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13641, uu____13642) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13636 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13635 in
                                  quant xy uu____13634 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13625) in
                              let uu____13651 =
                                let uu____13666 =
                                  let uu____13679 =
                                    let uu____13688 =
                                      let uu____13689 =
                                        let uu____13690 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13690 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13689 in
                                    quant qx uu____13688 in
                                  (FStar_Parser_Const.op_Minus, uu____13679) in
                                let uu____13699 =
                                  let uu____13714 =
                                    let uu____13727 =
                                      let uu____13736 =
                                        let uu____13737 =
                                          let uu____13738 =
                                            let uu____13743 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13744 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13743, uu____13744) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13738 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13737 in
                                      quant xy uu____13736 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13727) in
                                  let uu____13753 =
                                    let uu____13768 =
                                      let uu____13781 =
                                        let uu____13790 =
                                          let uu____13791 =
                                            let uu____13792 =
                                              let uu____13797 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13798 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13797, uu____13798) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13792 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13791 in
                                        quant xy uu____13790 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13781) in
                                    let uu____13807 =
                                      let uu____13822 =
                                        let uu____13835 =
                                          let uu____13844 =
                                            let uu____13845 =
                                              let uu____13846 =
                                                let uu____13851 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13852 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13851, uu____13852) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13846 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13845 in
                                          quant xy uu____13844 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13835) in
                                      let uu____13861 =
                                        let uu____13876 =
                                          let uu____13889 =
                                            let uu____13898 =
                                              let uu____13899 =
                                                let uu____13900 =
                                                  let uu____13905 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13906 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13905, uu____13906) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13900 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13899 in
                                            quant xy uu____13898 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13889) in
                                        let uu____13915 =
                                          let uu____13930 =
                                            let uu____13943 =
                                              let uu____13952 =
                                                let uu____13953 =
                                                  let uu____13954 =
                                                    let uu____13959 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13960 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13959,
                                                      uu____13960) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13954 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13953 in
                                              quant xy uu____13952 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13943) in
                                          let uu____13969 =
                                            let uu____13984 =
                                              let uu____13997 =
                                                let uu____14006 =
                                                  let uu____14007 =
                                                    let uu____14008 =
                                                      let uu____14013 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14014 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14013,
                                                        uu____14014) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14008 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14007 in
                                                quant xy uu____14006 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13997) in
                                            let uu____14023 =
                                              let uu____14038 =
                                                let uu____14051 =
                                                  let uu____14060 =
                                                    let uu____14061 =
                                                      let uu____14062 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14062 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14061 in
                                                  quant qx uu____14060 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14051) in
                                              [uu____14038] in
                                            uu____13984 :: uu____14023 in
                                          uu____13930 :: uu____13969 in
                                        uu____13876 :: uu____13915 in
                                      uu____13822 :: uu____13861 in
                                    uu____13768 :: uu____13807 in
                                  uu____13714 :: uu____13753 in
                                uu____13666 :: uu____13699 in
                              uu____13612 :: uu____13651 in
                            uu____13558 :: uu____13597 in
                          uu____13504 :: uu____13543 in
                        uu____13450 :: uu____13489 in
                      uu____13396 :: uu____13435 in
                    uu____13348 :: uu____13381 in
                  uu____13301 :: uu____13333 in
                let mk1 l v1 =
                  let uu____14276 =
                    let uu____14285 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14343  ->
                              match uu____14343 with
                              | (l',uu____14357) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14285
                      (FStar_Option.map
                         (fun uu____14417  ->
                            match uu____14417 with | (uu____14436,b) -> b v1)) in
                  FStar_All.pipe_right uu____14276 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14507  ->
                          match uu____14507 with
                          | (l',uu____14521) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14559 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14559 with
        | (xxsym,xx) ->
            let uu____14566 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14566 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14576 =
                   let uu____14583 =
                     let uu____14584 =
                       let uu____14595 =
                         let uu____14596 =
                           let uu____14601 =
                             let uu____14602 =
                               let uu____14607 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14607) in
                             FStar_SMTEncoding_Util.mkEq uu____14602 in
                           (xx_has_type, uu____14601) in
                         FStar_SMTEncoding_Util.mkImp uu____14596 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14595) in
                     FStar_SMTEncoding_Util.mkForall uu____14584 in
                   let uu____14632 =
                     let uu____14633 =
                       let uu____14634 =
                         let uu____14635 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14635 in
                       Prims.strcat module_name uu____14634 in
                     varops.mk_unique uu____14633 in
                   (uu____14583, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14632) in
                 FStar_SMTEncoding_Util.mkAssume uu____14576)
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
    let uu____14671 =
      let uu____14672 =
        let uu____14679 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14679, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14672 in
    let uu____14682 =
      let uu____14685 =
        let uu____14686 =
          let uu____14693 =
            let uu____14694 =
              let uu____14705 =
                let uu____14706 =
                  let uu____14711 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14711) in
                FStar_SMTEncoding_Util.mkImp uu____14706 in
              ([[typing_pred]], [xx], uu____14705) in
            mkForall_fuel uu____14694 in
          (uu____14693, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14686 in
      [uu____14685] in
    uu____14671 :: uu____14682 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14753 =
      let uu____14754 =
        let uu____14761 =
          let uu____14762 =
            let uu____14773 =
              let uu____14778 =
                let uu____14781 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14781] in
              [uu____14778] in
            let uu____14786 =
              let uu____14787 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14787 tt in
            (uu____14773, [bb], uu____14786) in
          FStar_SMTEncoding_Util.mkForall uu____14762 in
        (uu____14761, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14754 in
    let uu____14808 =
      let uu____14811 =
        let uu____14812 =
          let uu____14819 =
            let uu____14820 =
              let uu____14831 =
                let uu____14832 =
                  let uu____14837 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14837) in
                FStar_SMTEncoding_Util.mkImp uu____14832 in
              ([[typing_pred]], [xx], uu____14831) in
            mkForall_fuel uu____14820 in
          (uu____14819, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14812 in
      [uu____14811] in
    uu____14753 :: uu____14808 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14887 =
        let uu____14888 =
          let uu____14895 =
            let uu____14898 =
              let uu____14901 =
                let uu____14904 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14905 =
                  let uu____14908 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14908] in
                uu____14904 :: uu____14905 in
              tt :: uu____14901 in
            tt :: uu____14898 in
          ("Prims.Precedes", uu____14895) in
        FStar_SMTEncoding_Util.mkApp uu____14888 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14887 in
    let precedes_y_x =
      let uu____14912 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14912 in
    let uu____14915 =
      let uu____14916 =
        let uu____14923 =
          let uu____14924 =
            let uu____14935 =
              let uu____14940 =
                let uu____14943 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14943] in
              [uu____14940] in
            let uu____14948 =
              let uu____14949 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14949 tt in
            (uu____14935, [bb], uu____14948) in
          FStar_SMTEncoding_Util.mkForall uu____14924 in
        (uu____14923, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14916 in
    let uu____14970 =
      let uu____14973 =
        let uu____14974 =
          let uu____14981 =
            let uu____14982 =
              let uu____14993 =
                let uu____14994 =
                  let uu____14999 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14999) in
                FStar_SMTEncoding_Util.mkImp uu____14994 in
              ([[typing_pred]], [xx], uu____14993) in
            mkForall_fuel uu____14982 in
          (uu____14981, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14974 in
      let uu____15024 =
        let uu____15027 =
          let uu____15028 =
            let uu____15035 =
              let uu____15036 =
                let uu____15047 =
                  let uu____15048 =
                    let uu____15053 =
                      let uu____15054 =
                        let uu____15057 =
                          let uu____15060 =
                            let uu____15063 =
                              let uu____15064 =
                                let uu____15069 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15070 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15069, uu____15070) in
                              FStar_SMTEncoding_Util.mkGT uu____15064 in
                            let uu____15071 =
                              let uu____15074 =
                                let uu____15075 =
                                  let uu____15080 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15081 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15080, uu____15081) in
                                FStar_SMTEncoding_Util.mkGTE uu____15075 in
                              let uu____15082 =
                                let uu____15085 =
                                  let uu____15086 =
                                    let uu____15091 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15092 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15091, uu____15092) in
                                  FStar_SMTEncoding_Util.mkLT uu____15086 in
                                [uu____15085] in
                              uu____15074 :: uu____15082 in
                            uu____15063 :: uu____15071 in
                          typing_pred_y :: uu____15060 in
                        typing_pred :: uu____15057 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15054 in
                    (uu____15053, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15048 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15047) in
              mkForall_fuel uu____15036 in
            (uu____15035,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15028 in
        [uu____15027] in
      uu____14973 :: uu____15024 in
    uu____14915 :: uu____14970 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15138 =
      let uu____15139 =
        let uu____15146 =
          let uu____15147 =
            let uu____15158 =
              let uu____15163 =
                let uu____15166 = FStar_SMTEncoding_Term.boxString b in
                [uu____15166] in
              [uu____15163] in
            let uu____15171 =
              let uu____15172 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15172 tt in
            (uu____15158, [bb], uu____15171) in
          FStar_SMTEncoding_Util.mkForall uu____15147 in
        (uu____15146, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15139 in
    let uu____15193 =
      let uu____15196 =
        let uu____15197 =
          let uu____15204 =
            let uu____15205 =
              let uu____15216 =
                let uu____15217 =
                  let uu____15222 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15222) in
                FStar_SMTEncoding_Util.mkImp uu____15217 in
              ([[typing_pred]], [xx], uu____15216) in
            mkForall_fuel uu____15205 in
          (uu____15204, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15197 in
      [uu____15196] in
    uu____15138 :: uu____15193 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15275 =
      let uu____15276 =
        let uu____15283 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15283, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15276 in
    [uu____15275] in
  let mk_and_interp env conj uu____15295 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15320 =
      let uu____15321 =
        let uu____15328 =
          let uu____15329 =
            let uu____15340 =
              let uu____15341 =
                let uu____15346 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15346, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15341 in
            ([[l_and_a_b]], [aa; bb], uu____15340) in
          FStar_SMTEncoding_Util.mkForall uu____15329 in
        (uu____15328, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15321 in
    [uu____15320] in
  let mk_or_interp env disj uu____15384 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15409 =
      let uu____15410 =
        let uu____15417 =
          let uu____15418 =
            let uu____15429 =
              let uu____15430 =
                let uu____15435 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15435, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15430 in
            ([[l_or_a_b]], [aa; bb], uu____15429) in
          FStar_SMTEncoding_Util.mkForall uu____15418 in
        (uu____15417, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15410 in
    [uu____15409] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15498 =
      let uu____15499 =
        let uu____15506 =
          let uu____15507 =
            let uu____15518 =
              let uu____15519 =
                let uu____15524 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15524, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15519 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15518) in
          FStar_SMTEncoding_Util.mkForall uu____15507 in
        (uu____15506, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15499 in
    [uu____15498] in
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
    let uu____15597 =
      let uu____15598 =
        let uu____15605 =
          let uu____15606 =
            let uu____15617 =
              let uu____15618 =
                let uu____15623 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15623, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15618 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15617) in
          FStar_SMTEncoding_Util.mkForall uu____15606 in
        (uu____15605, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15598 in
    [uu____15597] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15694 =
      let uu____15695 =
        let uu____15702 =
          let uu____15703 =
            let uu____15714 =
              let uu____15715 =
                let uu____15720 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15720, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15715 in
            ([[l_imp_a_b]], [aa; bb], uu____15714) in
          FStar_SMTEncoding_Util.mkForall uu____15703 in
        (uu____15702, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15695 in
    [uu____15694] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15783 =
      let uu____15784 =
        let uu____15791 =
          let uu____15792 =
            let uu____15803 =
              let uu____15804 =
                let uu____15809 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15809, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15804 in
            ([[l_iff_a_b]], [aa; bb], uu____15803) in
          FStar_SMTEncoding_Util.mkForall uu____15792 in
        (uu____15791, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15784 in
    [uu____15783] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15861 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15861 in
    let uu____15864 =
      let uu____15865 =
        let uu____15872 =
          let uu____15873 =
            let uu____15884 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15884) in
          FStar_SMTEncoding_Util.mkForall uu____15873 in
        (uu____15872, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15865 in
    [uu____15864] in
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
      let uu____15944 =
        let uu____15951 =
          let uu____15954 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15954] in
        ("Valid", uu____15951) in
      FStar_SMTEncoding_Util.mkApp uu____15944 in
    let uu____15957 =
      let uu____15958 =
        let uu____15965 =
          let uu____15966 =
            let uu____15977 =
              let uu____15978 =
                let uu____15983 =
                  let uu____15984 =
                    let uu____15995 =
                      let uu____16000 =
                        let uu____16003 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16003] in
                      [uu____16000] in
                    let uu____16008 =
                      let uu____16009 =
                        let uu____16014 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16014, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16009 in
                    (uu____15995, [xx1], uu____16008) in
                  FStar_SMTEncoding_Util.mkForall uu____15984 in
                (uu____15983, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15978 in
            ([[l_forall_a_b]], [aa; bb], uu____15977) in
          FStar_SMTEncoding_Util.mkForall uu____15966 in
        (uu____15965, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15958 in
    [uu____15957] in
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
      let uu____16096 =
        let uu____16103 =
          let uu____16106 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16106] in
        ("Valid", uu____16103) in
      FStar_SMTEncoding_Util.mkApp uu____16096 in
    let uu____16109 =
      let uu____16110 =
        let uu____16117 =
          let uu____16118 =
            let uu____16129 =
              let uu____16130 =
                let uu____16135 =
                  let uu____16136 =
                    let uu____16147 =
                      let uu____16152 =
                        let uu____16155 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16155] in
                      [uu____16152] in
                    let uu____16160 =
                      let uu____16161 =
                        let uu____16166 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16166, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16161 in
                    (uu____16147, [xx1], uu____16160) in
                  FStar_SMTEncoding_Util.mkExists uu____16136 in
                (uu____16135, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16130 in
            ([[l_exists_a_b]], [aa; bb], uu____16129) in
          FStar_SMTEncoding_Util.mkForall uu____16118 in
        (uu____16117, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16110 in
    [uu____16109] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16226 =
      let uu____16227 =
        let uu____16234 =
          let uu____16235 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16235 range_ty in
        let uu____16236 = varops.mk_unique "typing_range_const" in
        (uu____16234, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16236) in
      FStar_SMTEncoding_Util.mkAssume uu____16227 in
    [uu____16226] in
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
        let uu____16270 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16270 x1 t in
      let uu____16271 =
        let uu____16282 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16282) in
      FStar_SMTEncoding_Util.mkForall uu____16271 in
    let uu____16305 =
      let uu____16306 =
        let uu____16313 =
          let uu____16314 =
            let uu____16325 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16325) in
          FStar_SMTEncoding_Util.mkForall uu____16314 in
        (uu____16313,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16306 in
    [uu____16305] in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e]) in
    let uu____16375 =
      let uu____16376 =
        let uu____16383 =
          let uu____16384 =
            let uu____16399 =
              let uu____16400 =
                let uu____16405 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____16406 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____16405, uu____16406) in
              FStar_SMTEncoding_Util.mkAnd uu____16400 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16399) in
          FStar_SMTEncoding_Util.mkForall' uu____16384 in
        (uu____16383,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____16376 in
    [uu____16375] in
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
          let uu____16752 =
            FStar_Util.find_opt
              (fun uu____16778  ->
                 match uu____16778 with
                 | (l,uu____16790) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16752 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16815,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16851 = encode_function_type_as_formula t env in
        match uu____16851 with
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
              let uu____16891 =
                ((let uu____16894 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16894) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16891
              then
                let uu____16901 = new_term_constant_and_tok_from_lid env lid in
                match uu____16901 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16920 =
                        let uu____16921 = FStar_Syntax_Subst.compress t_norm in
                        uu____16921.FStar_Syntax_Syntax.n in
                      match uu____16920 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16927) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16957  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16962 -> [] in
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
                (let uu____16976 = prims.is lid in
                 if uu____16976
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16984 = prims.mk lid vname in
                   match uu____16984 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17008 =
                      let uu____17019 = curried_arrow_formals_comp t_norm in
                      match uu____17019 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17037 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17037
                            then
                              let uu____17038 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___119_17041 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___119_17041.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___119_17041.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___119_17041.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___119_17041.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___119_17041.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___119_17041.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___119_17041.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___119_17041.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___119_17041.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___119_17041.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___119_17041.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___119_17041.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___119_17041.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___119_17041.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___119_17041.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___119_17041.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___119_17041.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___119_17041.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___119_17041.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___119_17041.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___119_17041.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___119_17041.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___119_17041.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___119_17041.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___119_17041.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___119_17041.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___119_17041.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___119_17041.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___119_17041.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___119_17041.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___119_17041.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___119_17041.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___119_17041.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___119_17041.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17038
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17053 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17053)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17008 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17098 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17098 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17119 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___91_17161  ->
                                       match uu___91_17161 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17165 =
                                             FStar_Util.prefix vars in
                                           (match uu____17165 with
                                            | (uu____17186,(xxsym,uu____17188))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17206 =
                                                  let uu____17207 =
                                                    let uu____17214 =
                                                      let uu____17215 =
                                                        let uu____17226 =
                                                          let uu____17227 =
                                                            let uu____17232 =
                                                              let uu____17233
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17233 in
                                                            (vapp,
                                                              uu____17232) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17227 in
                                                        ([[vapp]], vars,
                                                          uu____17226) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17215 in
                                                    (uu____17214,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17207 in
                                                [uu____17206])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17252 =
                                             FStar_Util.prefix vars in
                                           (match uu____17252 with
                                            | (uu____17273,(xxsym,uu____17275))
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
                                                let uu____17298 =
                                                  let uu____17299 =
                                                    let uu____17306 =
                                                      let uu____17307 =
                                                        let uu____17318 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17318) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17307 in
                                                    (uu____17306,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17299 in
                                                [uu____17298])
                                       | uu____17335 -> [])) in
                             let uu____17336 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17336 with
                              | (vars,guards,env',decls1,uu____17363) ->
                                  let uu____17376 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17385 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17385, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17387 =
                                          encode_formula p env' in
                                        (match uu____17387 with
                                         | (g,ds) ->
                                             let uu____17398 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17398,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17376 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17411 =
                                           let uu____17418 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17418) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17411 in
                                       let uu____17427 =
                                         let vname_decl =
                                           let uu____17435 =
                                             let uu____17446 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17456  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17446,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17435 in
                                         let uu____17465 =
                                           let env2 =
                                             let uu___120_17471 = env1 in
                                             {
                                               bindings =
                                                 (uu___120_17471.bindings);
                                               depth = (uu___120_17471.depth);
                                               tcenv = (uu___120_17471.tcenv);
                                               warn = (uu___120_17471.warn);
                                               cache = (uu___120_17471.cache);
                                               nolabels =
                                                 (uu___120_17471.nolabels);
                                               use_zfuel_name =
                                                 (uu___120_17471.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___120_17471.current_module_name)
                                             } in
                                           let uu____17472 =
                                             let uu____17473 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17473 in
                                           if uu____17472
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17465 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17488::uu____17489 ->
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
                                                     let uu____17529 =
                                                       let uu____17540 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17540) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17529 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17567 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17570 =
                                               match formals with
                                               | [] ->
                                                   let uu____17587 =
                                                     let uu____17588 =
                                                       let uu____17591 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17591 in
                                                     push_free_var env1 lid
                                                       vname uu____17588 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17587)
                                               | uu____17596 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17603 =
                                                       let uu____17610 =
                                                         let uu____17611 =
                                                           let uu____17622 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17622) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17611 in
                                                       (uu____17610,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17603 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17570 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17427 with
                                        | (decls2,env2) ->
                                            let uu____17665 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17673 =
                                                encode_term res_t1 env' in
                                              match uu____17673 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17686 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17686, decls) in
                                            (match uu____17665 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17697 =
                                                     let uu____17704 =
                                                       let uu____17705 =
                                                         let uu____17716 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17716) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17705 in
                                                     (uu____17704,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17697 in
                                                 let freshness =
                                                   let uu____17732 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17732
                                                   then
                                                     let uu____17737 =
                                                       let uu____17738 =
                                                         let uu____17749 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17760 =
                                                           varops.next_id () in
                                                         (vname, uu____17749,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17760) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17738 in
                                                     let uu____17763 =
                                                       let uu____17766 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17766] in
                                                     uu____17737 ::
                                                       uu____17763
                                                   else [] in
                                                 let g =
                                                   let uu____17771 =
                                                     let uu____17774 =
                                                       let uu____17777 =
                                                         let uu____17780 =
                                                           let uu____17783 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17783 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17780 in
                                                       FStar_List.append
                                                         decls3 uu____17777 in
                                                     FStar_List.append decls2
                                                       uu____17774 in
                                                   FStar_List.append decls11
                                                     uu____17771 in
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
          let uu____17814 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17814 with
          | FStar_Pervasives_Native.None  ->
              let uu____17851 = encode_free_var false env x t t_norm [] in
              (match uu____17851 with
               | (decls,env1) ->
                   let uu____17878 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17878 with
                    | (n1,x',uu____17905) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17926) ->
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
            let uu____17981 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17981 with
            | (decls,env1) ->
                let uu____18000 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18000
                then
                  let uu____18007 =
                    let uu____18010 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18010 in
                  (uu____18007, env1)
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
             (fun uu____18062  ->
                fun lb  ->
                  match uu____18062 with
                  | (decls,env1) ->
                      let uu____18082 =
                        let uu____18089 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18089
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18082 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18110 = FStar_Syntax_Util.head_and_args t in
    match uu____18110 with
    | (hd1,args) ->
        let uu____18147 =
          let uu____18148 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18148.FStar_Syntax_Syntax.n in
        (match uu____18147 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18152,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18171 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18193  ->
      fun quals  ->
        match uu____18193 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18269 = FStar_Util.first_N nbinders formals in
              match uu____18269 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18350  ->
                         fun uu____18351  ->
                           match (uu____18350, uu____18351) with
                           | ((formal,uu____18369),(binder,uu____18371)) ->
                               let uu____18380 =
                                 let uu____18387 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18387) in
                               FStar_Syntax_Syntax.NT uu____18380) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18395 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18426  ->
                              match uu____18426 with
                              | (x,i) ->
                                  let uu____18437 =
                                    let uu___121_18438 = x in
                                    let uu____18439 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_18438.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_18438.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18439
                                    } in
                                  (uu____18437, i))) in
                    FStar_All.pipe_right uu____18395
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18457 =
                      let uu____18458 = FStar_Syntax_Subst.compress body in
                      let uu____18459 =
                        let uu____18460 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18460 in
                      FStar_Syntax_Syntax.extend_app_n uu____18458
                        uu____18459 in
                    uu____18457 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18521 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18521
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___122_18524 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_18524.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_18524.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_18524.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_18524.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_18524.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_18524.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_18524.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_18524.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_18524.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_18524.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_18524.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_18524.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_18524.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_18524.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_18524.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_18524.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_18524.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_18524.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_18524.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___122_18524.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___122_18524.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___122_18524.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_18524.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_18524.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___122_18524.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_18524.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_18524.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___122_18524.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___122_18524.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_18524.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___122_18524.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___122_18524.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___122_18524.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___122_18524.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18557 = FStar_Syntax_Util.abs_formals e in
                match uu____18557 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18621::uu____18622 ->
                         let uu____18637 =
                           let uu____18638 =
                             let uu____18641 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18641 in
                           uu____18638.FStar_Syntax_Syntax.n in
                         (match uu____18637 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18684 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18684 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18726 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18726
                                   then
                                     let uu____18761 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18761 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18855  ->
                                                   fun uu____18856  ->
                                                     match (uu____18855,
                                                             uu____18856)
                                                     with
                                                     | ((x,uu____18874),
                                                        (b,uu____18876)) ->
                                                         let uu____18885 =
                                                           let uu____18892 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18892) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18885)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18894 =
                                            let uu____18915 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18915) in
                                          (uu____18894, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18983 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18983 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19072) ->
                              let uu____19077 =
                                let uu____19098 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19098 in
                              (uu____19077, true)
                          | uu____19163 when Prims.op_Negation norm1 ->
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
                          | uu____19165 ->
                              let uu____19166 =
                                let uu____19167 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19168 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19167
                                  uu____19168 in
                              failwith uu____19166)
                     | uu____19193 ->
                         let rec aux' t_norm2 =
                           let uu____19218 =
                             let uu____19219 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19219.FStar_Syntax_Syntax.n in
                           match uu____19218 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19260 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19260 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19288 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19288 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19368)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19373 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19429 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19429
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19441 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19535  ->
                            fun lb  ->
                              match uu____19535 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19630 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19630
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19633 =
                                      let uu____19648 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19648
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19633 with
                                    | (tok,decl,env2) ->
                                        let uu____19694 =
                                          let uu____19707 =
                                            let uu____19718 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19718, tok) in
                                          uu____19707 :: toks in
                                        (uu____19694, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19441 with
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
                        | uu____19901 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19909 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19909 vars)
                            else
                              (let uu____19911 =
                                 let uu____19918 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19918) in
                               FStar_SMTEncoding_Util.mkApp uu____19911) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20000;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20002;
                             FStar_Syntax_Syntax.lbeff = uu____20003;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____20005;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20071 =
                              let uu____20078 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20078 with
                              | (tcenv',uu____20096,e_t) ->
                                  let uu____20102 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20113 -> failwith "Impossible" in
                                  (match uu____20102 with
                                   | (e1,t_norm1) ->
                                       ((let uu___125_20129 = env2 in
                                         {
                                           bindings =
                                             (uu___125_20129.bindings);
                                           depth = (uu___125_20129.depth);
                                           tcenv = tcenv';
                                           warn = (uu___125_20129.warn);
                                           cache = (uu___125_20129.cache);
                                           nolabels =
                                             (uu___125_20129.nolabels);
                                           use_zfuel_name =
                                             (uu___125_20129.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___125_20129.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___125_20129.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20071 with
                             | (env',e1,t_norm1) ->
                                 let uu____20139 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20139 with
                                  | ((binders,body,uu____20160,uu____20161),curry)
                                      ->
                                      ((let uu____20172 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20172
                                        then
                                          let uu____20173 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20174 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20173 uu____20174
                                        else ());
                                       (let uu____20176 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20176 with
                                        | (vars,guards,env'1,binder_decls,uu____20203)
                                            ->
                                            let body1 =
                                              let uu____20217 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20217
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20220 =
                                              let uu____20229 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20229
                                              then
                                                let uu____20240 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20241 =
                                                  encode_formula body1 env'1 in
                                                (uu____20240, uu____20241)
                                              else
                                                (let uu____20251 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20251)) in
                                            (match uu____20220 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20274 =
                                                     let uu____20281 =
                                                       let uu____20282 =
                                                         let uu____20293 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20293) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20282 in
                                                     let uu____20304 =
                                                       let uu____20307 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20307 in
                                                     (uu____20281,
                                                       uu____20304,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20274 in
                                                 let uu____20310 =
                                                   let uu____20313 =
                                                     let uu____20316 =
                                                       let uu____20319 =
                                                         let uu____20322 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20322 in
                                                       FStar_List.append
                                                         decls2 uu____20319 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20316 in
                                                   FStar_List.append decls1
                                                     uu____20313 in
                                                 (uu____20310, env2))))))
                        | uu____20327 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20412 = varops.fresh "fuel" in
                          (uu____20412, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20415 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20503  ->
                                  fun uu____20504  ->
                                    match (uu____20503, uu____20504) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20652 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20652 in
                                        let gtok =
                                          let uu____20654 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20654 in
                                        let env4 =
                                          let uu____20656 =
                                            let uu____20659 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20659 in
                                          push_free_var env3 flid gtok
                                            uu____20656 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20415 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20815 t_norm
                              uu____20817 =
                              match (uu____20815, uu____20817) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20861;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20862;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;
                                                        FStar_Syntax_Syntax.lbattrs
                                                          = uu____20864;_})
                                  ->
                                  let uu____20895 =
                                    let uu____20902 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20902 with
                                    | (tcenv',uu____20924,e_t) ->
                                        let uu____20930 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20941 ->
                                              failwith "Impossible" in
                                        (match uu____20930 with
                                         | (e1,t_norm1) ->
                                             ((let uu___126_20957 = env3 in
                                               {
                                                 bindings =
                                                   (uu___126_20957.bindings);
                                                 depth =
                                                   (uu___126_20957.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___126_20957.warn);
                                                 cache =
                                                   (uu___126_20957.cache);
                                                 nolabels =
                                                   (uu___126_20957.nolabels);
                                                 use_zfuel_name =
                                                   (uu___126_20957.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___126_20957.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___126_20957.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20895 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20972 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20972
                                         then
                                           let uu____20973 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20974 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20975 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20973 uu____20974
                                             uu____20975
                                         else ());
                                        (let uu____20977 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20977 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21014 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21014
                                               then
                                                 let uu____21015 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21016 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21017 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21018 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21015 uu____21016
                                                   uu____21017 uu____21018
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21022 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21022 with
                                               | (vars,guards,env'1,binder_decls,uu____21053)
                                                   ->
                                                   let decl_g =
                                                     let uu____21067 =
                                                       let uu____21078 =
                                                         let uu____21081 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21081 in
                                                       (g, uu____21078,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21067 in
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
                                                     let uu____21106 =
                                                       let uu____21113 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21113) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21106 in
                                                   let gsapp =
                                                     let uu____21123 =
                                                       let uu____21130 =
                                                         let uu____21133 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21133 ::
                                                           vars_tm in
                                                       (g, uu____21130) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21123 in
                                                   let gmax =
                                                     let uu____21139 =
                                                       let uu____21146 =
                                                         let uu____21149 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21149 ::
                                                           vars_tm in
                                                       (g, uu____21146) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21139 in
                                                   let body1 =
                                                     let uu____21155 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21155
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21157 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21157 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21175 =
                                                            let uu____21182 =
                                                              let uu____21183
                                                                =
                                                                let uu____21198
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
                                                                  uu____21198) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21183 in
                                                            let uu____21219 =
                                                              let uu____21222
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21222 in
                                                            (uu____21182,
                                                              uu____21219,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21175 in
                                                        let eqn_f =
                                                          let uu____21226 =
                                                            let uu____21233 =
                                                              let uu____21234
                                                                =
                                                                let uu____21245
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21245) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21234 in
                                                            (uu____21233,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21226 in
                                                        let eqn_g' =
                                                          let uu____21259 =
                                                            let uu____21266 =
                                                              let uu____21267
                                                                =
                                                                let uu____21278
                                                                  =
                                                                  let uu____21279
                                                                    =
                                                                    let uu____21284
                                                                    =
                                                                    let uu____21285
                                                                    =
                                                                    let uu____21292
                                                                    =
                                                                    let uu____21295
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21295
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21292) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21285 in
                                                                    (gsapp,
                                                                    uu____21284) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21279 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21278) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21267 in
                                                            (uu____21266,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21259 in
                                                        let uu____21318 =
                                                          let uu____21327 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21327
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21356)
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
                                                                  let uu____21381
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21381
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21386
                                                                  =
                                                                  let uu____21393
                                                                    =
                                                                    let uu____21394
                                                                    =
                                                                    let uu____21405
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21405) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21394 in
                                                                  (uu____21393,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21386 in
                                                              let uu____21426
                                                                =
                                                                let uu____21433
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21433
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21446
                                                                    =
                                                                    let uu____21449
                                                                    =
                                                                    let uu____21450
                                                                    =
                                                                    let uu____21457
                                                                    =
                                                                    let uu____21458
                                                                    =
                                                                    let uu____21469
                                                                    =
                                                                    let uu____21470
                                                                    =
                                                                    let uu____21475
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21475,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21470 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21469) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21458 in
                                                                    (uu____21457,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21450 in
                                                                    [uu____21449] in
                                                                    (d3,
                                                                    uu____21446) in
                                                              (match uu____21426
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21318
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
                            let uu____21540 =
                              let uu____21553 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21632  ->
                                   fun uu____21633  ->
                                     match (uu____21632, uu____21633) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21788 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21788 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21553 in
                            (match uu____21540 with
                             | (decls2,eqns,env01) ->
                                 let uu____21861 =
                                   let isDeclFun uu___92_21873 =
                                     match uu___92_21873 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21874 -> true
                                     | uu____21885 -> false in
                                   let uu____21886 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21886
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21861 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21926 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___93_21930  ->
                                 match uu___93_21930 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21931 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21937 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21937))) in
                      if uu____21926
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
                   let uu____21989 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21989
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
        let uu____22038 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22038 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22042 = encode_sigelt' env se in
      match uu____22042 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22058 =
                  let uu____22059 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22059 in
                [uu____22058]
            | uu____22060 ->
                let uu____22061 =
                  let uu____22064 =
                    let uu____22065 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22065 in
                  uu____22064 :: g in
                let uu____22066 =
                  let uu____22069 =
                    let uu____22070 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22070 in
                  [uu____22069] in
                FStar_List.append uu____22061 uu____22066 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22083 =
          let uu____22084 = FStar_Syntax_Subst.compress t in
          uu____22084.FStar_Syntax_Syntax.n in
        match uu____22083 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22088)) -> s = "opaque_to_smt"
        | uu____22089 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22094 =
          let uu____22095 = FStar_Syntax_Subst.compress t in
          uu____22095.FStar_Syntax_Syntax.n in
        match uu____22094 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22099)) -> s = "uninterpreted_by_smt"
        | uu____22100 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22105 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22110 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22113 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22116 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22131 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22135 =
            let uu____22136 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22136 Prims.op_Negation in
          if uu____22135
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22162 ->
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
               let uu____22182 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22182 with
               | (aname,atok,env2) ->
                   let uu____22198 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22198 with
                    | (formals,uu____22216) ->
                        let uu____22229 =
                          let uu____22234 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22234 env2 in
                        (match uu____22229 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22246 =
                                 let uu____22247 =
                                   let uu____22258 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22274  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22258,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22247 in
                               [uu____22246;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22287 =
                               let aux uu____22339 uu____22340 =
                                 match (uu____22339, uu____22340) with
                                 | ((bv,uu____22392),(env3,acc_sorts,acc)) ->
                                     let uu____22430 = gen_term_var env3 bv in
                                     (match uu____22430 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22287 with
                              | (uu____22502,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22525 =
                                      let uu____22532 =
                                        let uu____22533 =
                                          let uu____22544 =
                                            let uu____22545 =
                                              let uu____22550 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22550) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22545 in
                                          ([[app]], xs_sorts, uu____22544) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22533 in
                                      (uu____22532,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22525 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22570 =
                                      let uu____22577 =
                                        let uu____22578 =
                                          let uu____22589 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22589) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22578 in
                                      (uu____22577,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22570 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22608 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22608 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22636,uu____22637)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22638 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22638 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22655,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22661 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___94_22665  ->
                      match uu___94_22665 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22666 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22671 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22672 -> false)) in
            Prims.op_Negation uu____22661 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22681 =
               let uu____22688 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22688 env fv t quals in
             match uu____22681 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22703 =
                   let uu____22706 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22706 in
                 (uu____22703, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22714 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22714 with
           | (uu____22723,f1) ->
               let uu____22725 = encode_formula f1 env in
               (match uu____22725 with
                | (f2,decls) ->
                    let g =
                      let uu____22739 =
                        let uu____22740 =
                          let uu____22747 =
                            let uu____22750 =
                              let uu____22751 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22751 in
                            FStar_Pervasives_Native.Some uu____22750 in
                          let uu____22752 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22747, uu____22752) in
                        FStar_SMTEncoding_Util.mkAssume uu____22740 in
                      [uu____22739] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22758) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22770 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22788 =
                       let uu____22791 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22791.FStar_Syntax_Syntax.fv_name in
                     uu____22788.FStar_Syntax_Syntax.v in
                   let uu____22792 =
                     let uu____22793 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22793 in
                   if uu____22792
                   then
                     let val_decl =
                       let uu___129_22821 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___129_22821.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___129_22821.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___129_22821.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22826 = encode_sigelt' env1 val_decl in
                     match uu____22826 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22770 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22854,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22856;
                          FStar_Syntax_Syntax.lbtyp = uu____22857;
                          FStar_Syntax_Syntax.lbeff = uu____22858;
                          FStar_Syntax_Syntax.lbdef = uu____22859;
                          FStar_Syntax_Syntax.lbattrs = uu____22860;_}::[]),uu____22861)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22884 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22884 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22913 =
                   let uu____22916 =
                     let uu____22917 =
                       let uu____22924 =
                         let uu____22925 =
                           let uu____22936 =
                             let uu____22937 =
                               let uu____22942 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22942) in
                             FStar_SMTEncoding_Util.mkEq uu____22937 in
                           ([[b2t_x]], [xx], uu____22936) in
                         FStar_SMTEncoding_Util.mkForall uu____22925 in
                       (uu____22924,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22917 in
                   [uu____22916] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22913 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22975,uu____22976) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_22985  ->
                  match uu___95_22985 with
                  | FStar_Syntax_Syntax.Discriminator uu____22986 -> true
                  | uu____22987 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22990,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23001 =
                     let uu____23002 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23002.FStar_Ident.idText in
                   uu____23001 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___96_23006  ->
                     match uu___96_23006 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23007 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23011) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_23028  ->
                  match uu___97_23028 with
                  | FStar_Syntax_Syntax.Projector uu____23029 -> true
                  | uu____23034 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23037 = try_lookup_free_var env l in
          (match uu____23037 with
           | FStar_Pervasives_Native.Some uu____23044 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___130_23048 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___130_23048.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___130_23048.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___130_23048.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23055) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23073) ->
          let uu____23082 = encode_sigelts env ses in
          (match uu____23082 with
           | (g,env1) ->
               let uu____23099 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___98_23122  ->
                         match uu___98_23122 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23123;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23124;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23125;_}
                             -> false
                         | uu____23128 -> true)) in
               (match uu____23099 with
                | (g',inversions) ->
                    let uu____23143 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___99_23164  ->
                              match uu___99_23164 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23165 ->
                                  true
                              | uu____23176 -> false)) in
                    (match uu____23143 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23194,tps,k,uu____23197,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___100_23214  ->
                    match uu___100_23214 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23215 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23224 = c in
              match uu____23224 with
              | (name,args,uu____23229,uu____23230,uu____23231) ->
                  let uu____23236 =
                    let uu____23237 =
                      let uu____23248 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23265  ->
                                match uu____23265 with
                                | (uu____23272,sort,uu____23274) -> sort)) in
                      (name, uu____23248, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23237 in
                  [uu____23236]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23301 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23307 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23307 FStar_Option.isNone)) in
            if uu____23301
            then []
            else
              (let uu____23339 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23339 with
               | (xxsym,xx) ->
                   let uu____23348 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23387  ->
                             fun l  ->
                               match uu____23387 with
                               | (out,decls) ->
                                   let uu____23407 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23407 with
                                    | (uu____23418,data_t) ->
                                        let uu____23420 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23420 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23466 =
                                                 let uu____23467 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23467.FStar_Syntax_Syntax.n in
                                               match uu____23466 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23478,indices) ->
                                                   indices
                                               | uu____23500 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23524  ->
                                                         match uu____23524
                                                         with
                                                         | (x,uu____23530) ->
                                                             let uu____23531
                                                               =
                                                               let uu____23532
                                                                 =
                                                                 let uu____23539
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23539,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23532 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23531)
                                                    env) in
                                             let uu____23542 =
                                               encode_args indices env1 in
                                             (match uu____23542 with
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
                                                      let uu____23568 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23584
                                                                 =
                                                                 let uu____23589
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23589,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23584)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23568
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23592 =
                                                      let uu____23593 =
                                                        let uu____23598 =
                                                          let uu____23599 =
                                                            let uu____23604 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23604,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23599 in
                                                        (out, uu____23598) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23593 in
                                                    (uu____23592,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23348 with
                    | (data_ax,decls) ->
                        let uu____23617 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23617 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23628 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23628 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23632 =
                                 let uu____23639 =
                                   let uu____23640 =
                                     let uu____23651 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23666 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23651,
                                       uu____23666) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23640 in
                                 let uu____23681 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23639,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23681) in
                               FStar_SMTEncoding_Util.mkAssume uu____23632 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23684 =
            let uu____23697 =
              let uu____23698 = FStar_Syntax_Subst.compress k in
              uu____23698.FStar_Syntax_Syntax.n in
            match uu____23697 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23743 -> (tps, k) in
          (match uu____23684 with
           | (formals,res) ->
               let uu____23766 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23766 with
                | (formals1,res1) ->
                    let uu____23777 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23777 with
                     | (vars,guards,env',binder_decls,uu____23802) ->
                         let uu____23815 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23815 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23834 =
                                  let uu____23841 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23841) in
                                FStar_SMTEncoding_Util.mkApp uu____23834 in
                              let uu____23850 =
                                let tname_decl =
                                  let uu____23860 =
                                    let uu____23861 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23893  ->
                                              match uu____23893 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23906 = varops.next_id () in
                                    (tname, uu____23861,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23906, false) in
                                  constructor_or_logic_type_decl uu____23860 in
                                let uu____23915 =
                                  match vars with
                                  | [] ->
                                      let uu____23928 =
                                        let uu____23929 =
                                          let uu____23932 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23932 in
                                        push_free_var env1 t tname
                                          uu____23929 in
                                      ([], uu____23928)
                                  | uu____23939 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23948 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23948 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23962 =
                                          let uu____23969 =
                                            let uu____23970 =
                                              let uu____23985 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23985) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23970 in
                                          (uu____23969,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23962 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23915 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23850 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24025 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24025 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24043 =
                                               let uu____24044 =
                                                 let uu____24051 =
                                                   let uu____24052 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24052 in
                                                 (uu____24051,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24044 in
                                             [uu____24043]
                                           else [] in
                                         let uu____24056 =
                                           let uu____24059 =
                                             let uu____24062 =
                                               let uu____24063 =
                                                 let uu____24070 =
                                                   let uu____24071 =
                                                     let uu____24082 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24082) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24071 in
                                                 (uu____24070,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24063 in
                                             [uu____24062] in
                                           FStar_List.append karr uu____24059 in
                                         FStar_List.append decls1 uu____24056 in
                                   let aux =
                                     let uu____24098 =
                                       let uu____24101 =
                                         inversion_axioms tapp vars in
                                       let uu____24104 =
                                         let uu____24107 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24107] in
                                       FStar_List.append uu____24101
                                         uu____24104 in
                                     FStar_List.append kindingAx uu____24098 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24114,uu____24115,uu____24116,uu____24117,uu____24118)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24126,t,uu____24128,n_tps,uu____24130) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24138 = new_term_constant_and_tok_from_lid env d in
          (match uu____24138 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24155 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24155 with
                | (formals,t_res) ->
                    let uu____24190 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24190 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24204 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24204 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24274 =
                                            mk_term_projector_name d x in
                                          (uu____24274,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24276 =
                                  let uu____24295 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24295, true) in
                                FStar_All.pipe_right uu____24276
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
                              let uu____24334 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24334 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24346::uu____24347 ->
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
                                         let uu____24392 =
                                           let uu____24403 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24403) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24392
                                     | uu____24428 -> tok_typing in
                                   let uu____24437 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24437 with
                                    | (vars',guards',env'',decls_formals,uu____24462)
                                        ->
                                        let uu____24475 =
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
                                        (match uu____24475 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24506 ->
                                                   let uu____24513 =
                                                     let uu____24514 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24514 in
                                                   [uu____24513] in
                                             let encode_elim uu____24524 =
                                               let uu____24525 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24525 with
                                               | (head1,args) ->
                                                   let uu____24568 =
                                                     let uu____24569 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24569.FStar_Syntax_Syntax.n in
                                                   (match uu____24568 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24579;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24580;_},uu____24581)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24587 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24587
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
                                                                 | uu____24630
                                                                    ->
                                                                    let uu____24631
                                                                    =
                                                                    let uu____24636
                                                                    =
                                                                    let uu____24637
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24637 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24636) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24631
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24653
                                                                    =
                                                                    let uu____24654
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24654 in
                                                                    if
                                                                    uu____24653
                                                                    then
                                                                    let uu____24667
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24667]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24669
                                                               =
                                                               let uu____24682
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24732
                                                                     ->
                                                                    fun
                                                                    uu____24733
                                                                     ->
                                                                    match 
                                                                    (uu____24732,
                                                                    uu____24733)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24828
                                                                    =
                                                                    let uu____24835
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24835 in
                                                                    (match uu____24828
                                                                    with
                                                                    | 
                                                                    (uu____24848,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24856
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24856
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24858
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24858
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
                                                                 uu____24682 in
                                                             (match uu____24669
                                                              with
                                                              | (uu____24873,arg_vars,elim_eqns_or_guards,uu____24876)
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
                                                                    let uu____24906
                                                                    =
                                                                    let uu____24913
                                                                    =
                                                                    let uu____24914
                                                                    =
                                                                    let uu____24925
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24936
                                                                    =
                                                                    let uu____24937
                                                                    =
                                                                    let uu____24942
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24942) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24937 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24925,
                                                                    uu____24936) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24914 in
                                                                    (uu____24913,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24906 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24965
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24965,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24967
                                                                    =
                                                                    let uu____24974
                                                                    =
                                                                    let uu____24975
                                                                    =
                                                                    let uu____24986
                                                                    =
                                                                    let uu____24991
                                                                    =
                                                                    let uu____24994
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24994] in
                                                                    [uu____24991] in
                                                                    let uu____24999
                                                                    =
                                                                    let uu____25000
                                                                    =
                                                                    let uu____25005
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25006
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25005,
                                                                    uu____25006) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25000 in
                                                                    (uu____24986,
                                                                    [x],
                                                                    uu____24999) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24975 in
                                                                    let uu____25025
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24974,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25025) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24967
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25032
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
                                                                    (let uu____25060
                                                                    =
                                                                    let uu____25061
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25061
                                                                    dapp1 in
                                                                    [uu____25060]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25032
                                                                    FStar_List.flatten in
                                                                    let uu____25068
                                                                    =
                                                                    let uu____25075
                                                                    =
                                                                    let uu____25076
                                                                    =
                                                                    let uu____25087
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25098
                                                                    =
                                                                    let uu____25099
                                                                    =
                                                                    let uu____25104
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25104) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25099 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25087,
                                                                    uu____25098) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25076 in
                                                                    (uu____25075,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25068) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25125 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25125
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
                                                                 | uu____25168
                                                                    ->
                                                                    let uu____25169
                                                                    =
                                                                    let uu____25174
                                                                    =
                                                                    let uu____25175
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25175 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25174) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25169
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25191
                                                                    =
                                                                    let uu____25192
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25192 in
                                                                    if
                                                                    uu____25191
                                                                    then
                                                                    let uu____25205
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25205]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25207
                                                               =
                                                               let uu____25220
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25270
                                                                     ->
                                                                    fun
                                                                    uu____25271
                                                                     ->
                                                                    match 
                                                                    (uu____25270,
                                                                    uu____25271)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25366
                                                                    =
                                                                    let uu____25373
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25373 in
                                                                    (match uu____25366
                                                                    with
                                                                    | 
                                                                    (uu____25386,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25394
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25394
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25396
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25396
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
                                                                 uu____25220 in
                                                             (match uu____25207
                                                              with
                                                              | (uu____25411,arg_vars,elim_eqns_or_guards,uu____25414)
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
                                                                    let uu____25444
                                                                    =
                                                                    let uu____25451
                                                                    =
                                                                    let uu____25452
                                                                    =
                                                                    let uu____25463
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25474
                                                                    =
                                                                    let uu____25475
                                                                    =
                                                                    let uu____25480
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25480) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25475 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25463,
                                                                    uu____25474) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25452 in
                                                                    (uu____25451,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25444 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25503
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25503,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25505
                                                                    =
                                                                    let uu____25512
                                                                    =
                                                                    let uu____25513
                                                                    =
                                                                    let uu____25524
                                                                    =
                                                                    let uu____25529
                                                                    =
                                                                    let uu____25532
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25532] in
                                                                    [uu____25529] in
                                                                    let uu____25537
                                                                    =
                                                                    let uu____25538
                                                                    =
                                                                    let uu____25543
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25544
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25543,
                                                                    uu____25544) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25538 in
                                                                    (uu____25524,
                                                                    [x],
                                                                    uu____25537) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25513 in
                                                                    let uu____25563
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25512,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25563) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25505
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25570
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
                                                                    (let uu____25598
                                                                    =
                                                                    let uu____25599
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25599
                                                                    dapp1 in
                                                                    [uu____25598]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25570
                                                                    FStar_List.flatten in
                                                                    let uu____25606
                                                                    =
                                                                    let uu____25613
                                                                    =
                                                                    let uu____25614
                                                                    =
                                                                    let uu____25625
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25636
                                                                    =
                                                                    let uu____25637
                                                                    =
                                                                    let uu____25642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25642) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25637 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25625,
                                                                    uu____25636) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25614 in
                                                                    (uu____25613,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25606) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25661 ->
                                                        ((let uu____25663 =
                                                            let uu____25668 =
                                                              let uu____25669
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25670
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25669
                                                                uu____25670 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25668) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25663);
                                                         ([], []))) in
                                             let uu____25675 = encode_elim () in
                                             (match uu____25675 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25695 =
                                                      let uu____25698 =
                                                        let uu____25701 =
                                                          let uu____25704 =
                                                            let uu____25707 =
                                                              let uu____25708
                                                                =
                                                                let uu____25719
                                                                  =
                                                                  let uu____25722
                                                                    =
                                                                    let uu____25723
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25723 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25722 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25719) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25708 in
                                                            [uu____25707] in
                                                          let uu____25728 =
                                                            let uu____25731 =
                                                              let uu____25734
                                                                =
                                                                let uu____25737
                                                                  =
                                                                  let uu____25740
                                                                    =
                                                                    let uu____25743
                                                                    =
                                                                    let uu____25746
                                                                    =
                                                                    let uu____25747
                                                                    =
                                                                    let uu____25754
                                                                    =
                                                                    let uu____25755
                                                                    =
                                                                    let uu____25766
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25766) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25755 in
                                                                    (uu____25754,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25747 in
                                                                    let uu____25779
                                                                    =
                                                                    let uu____25782
                                                                    =
                                                                    let uu____25783
                                                                    =
                                                                    let uu____25790
                                                                    =
                                                                    let uu____25791
                                                                    =
                                                                    let uu____25802
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25813
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25802,
                                                                    uu____25813) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25791 in
                                                                    (uu____25790,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25783 in
                                                                    [uu____25782] in
                                                                    uu____25746
                                                                    ::
                                                                    uu____25779 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25743 in
                                                                  FStar_List.append
                                                                    uu____25740
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25737 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25734 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25731 in
                                                          FStar_List.append
                                                            uu____25704
                                                            uu____25728 in
                                                        FStar_List.append
                                                          decls3 uu____25701 in
                                                      FStar_List.append
                                                        decls2 uu____25698 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25695 in
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
           (fun uu____25859  ->
              fun se  ->
                match uu____25859 with
                | (g,env1) ->
                    let uu____25879 = encode_sigelt env1 se in
                    (match uu____25879 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25936 =
        match uu____25936 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25968 ->
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
                 ((let uu____25974 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25974
                   then
                     let uu____25975 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25976 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25977 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25975 uu____25976 uu____25977
                   else ());
                  (let uu____25979 = encode_term t1 env1 in
                   match uu____25979 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25995 =
                         let uu____26002 =
                           let uu____26003 =
                             let uu____26004 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26004
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26003 in
                         new_term_constant_from_string env1 x uu____26002 in
                       (match uu____25995 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26020 = FStar_Options.log_queries () in
                              if uu____26020
                              then
                                let uu____26023 =
                                  let uu____26024 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26025 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26026 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26024 uu____26025 uu____26026 in
                                FStar_Pervasives_Native.Some uu____26023
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26042,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26056 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26056 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26079,se,uu____26081) ->
                 let uu____26086 = encode_sigelt env1 se in
                 (match uu____26086 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26103,se) ->
                 let uu____26109 = encode_sigelt env1 se in
                 (match uu____26109 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26126 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26126 with | (uu____26149,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26161 'Auu____26162 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26162,'Auu____26161)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26230  ->
              match uu____26230 with
              | (l,uu____26242,uu____26243) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26289  ->
              match uu____26289 with
              | (l,uu____26303,uu____26304) ->
                  let uu____26313 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26314 =
                    let uu____26317 =
                      let uu____26318 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26318 in
                    [uu____26317] in
                  uu____26313 :: uu____26314)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26343 =
      let uu____26346 =
        let uu____26347 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26350 =
          let uu____26351 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26351 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26347;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26350
        } in
      [uu____26346] in
    FStar_ST.op_Colon_Equals last_env uu____26343
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26381 = FStar_ST.op_Bang last_env in
      match uu____26381 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26408 ->
          let uu___131_26411 = e in
          let uu____26412 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___131_26411.bindings);
            depth = (uu___131_26411.depth);
            tcenv;
            warn = (uu___131_26411.warn);
            cache = (uu___131_26411.cache);
            nolabels = (uu___131_26411.nolabels);
            use_zfuel_name = (uu___131_26411.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_26411.encode_non_total_function_typ);
            current_module_name = uu____26412
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26416 = FStar_ST.op_Bang last_env in
    match uu____26416 with
    | [] -> failwith "Empty env stack"
    | uu____26442::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26471  ->
    let uu____26472 = FStar_ST.op_Bang last_env in
    match uu____26472 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___132_26506 = hd1 in
          {
            bindings = (uu___132_26506.bindings);
            depth = (uu___132_26506.depth);
            tcenv = (uu___132_26506.tcenv);
            warn = (uu___132_26506.warn);
            cache = refs;
            nolabels = (uu___132_26506.nolabels);
            use_zfuel_name = (uu___132_26506.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_26506.encode_non_total_function_typ);
            current_module_name = (uu___132_26506.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26532  ->
    let uu____26533 = FStar_ST.op_Bang last_env in
    match uu____26533 with
    | [] -> failwith "Popping an empty stack"
    | uu____26559::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26623::uu____26624,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___133_26632 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___133_26632.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___133_26632.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___133_26632.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26633 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26648 =
        let uu____26651 =
          let uu____26652 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26652 in
        let uu____26653 = open_fact_db_tags env in uu____26651 :: uu____26653 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26648
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
      let uu____26675 = encode_sigelt env se in
      match uu____26675 with
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
        let uu____26711 = FStar_Options.log_queries () in
        if uu____26711
        then
          let uu____26714 =
            let uu____26715 =
              let uu____26716 =
                let uu____26717 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26717 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26716 in
            FStar_SMTEncoding_Term.Caption uu____26715 in
          uu____26714 :: decls
        else decls in
      (let uu____26728 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26728
       then
         let uu____26729 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26729
       else ());
      (let env =
         let uu____26732 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26732 tcenv in
       let uu____26733 = encode_top_level_facts env se in
       match uu____26733 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26747 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26747)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26759 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26759
       then
         let uu____26760 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26760
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26795  ->
                 fun se  ->
                   match uu____26795 with
                   | (g,env2) ->
                       let uu____26815 = encode_top_level_facts env2 se in
                       (match uu____26815 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26838 =
         encode_signature
           (let uu___134_26847 = env in
            {
              bindings = (uu___134_26847.bindings);
              depth = (uu___134_26847.depth);
              tcenv = (uu___134_26847.tcenv);
              warn = false;
              cache = (uu___134_26847.cache);
              nolabels = (uu___134_26847.nolabels);
              use_zfuel_name = (uu___134_26847.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_26847.encode_non_total_function_typ);
              current_module_name = (uu___134_26847.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26838 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26864 = FStar_Options.log_queries () in
             if uu____26864
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___135_26872 = env1 in
               {
                 bindings = (uu___135_26872.bindings);
                 depth = (uu___135_26872.depth);
                 tcenv = (uu___135_26872.tcenv);
                 warn = true;
                 cache = (uu___135_26872.cache);
                 nolabels = (uu___135_26872.nolabels);
                 use_zfuel_name = (uu___135_26872.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___135_26872.encode_non_total_function_typ);
                 current_module_name = (uu___135_26872.current_module_name)
               });
            (let uu____26874 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26874
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
        (let uu____26926 =
           let uu____26927 = FStar_TypeChecker_Env.current_module tcenv in
           uu____26927.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26926);
        (let env =
           let uu____26929 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____26929 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____26941 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26976 = aux rest in
                 (match uu____26976 with
                  | (out,rest1) ->
                      let t =
                        let uu____27006 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27006 with
                        | FStar_Pervasives_Native.Some uu____27011 ->
                            let uu____27012 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27012
                              x.FStar_Syntax_Syntax.sort
                        | uu____27013 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27017 =
                        let uu____27020 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___136_27023 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_27023.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_27023.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27020 :: out in
                      (uu____27017, rest1))
             | uu____27028 -> ([], bindings1) in
           let uu____27035 = aux bindings in
           match uu____27035 with
           | (closing,bindings1) ->
               let uu____27060 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27060, bindings1) in
         match uu____26941 with
         | (q1,bindings1) ->
             let uu____27083 =
               let uu____27088 =
                 FStar_List.filter
                   (fun uu___101_27093  ->
                      match uu___101_27093 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27094 ->
                          false
                      | uu____27101 -> true) bindings1 in
               encode_env_bindings env uu____27088 in
             (match uu____27083 with
              | (env_decls,env1) ->
                  ((let uu____27119 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27119
                    then
                      let uu____27120 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27120
                    else ());
                   (let uu____27122 = encode_formula q1 env1 in
                    match uu____27122 with
                    | (phi,qdecls) ->
                        let uu____27143 =
                          let uu____27148 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27148 phi in
                        (match uu____27143 with
                         | (labels,phi1) ->
                             let uu____27165 = encode_labels labels in
                             (match uu____27165 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27202 =
                                      let uu____27209 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27210 =
                                        varops.mk_unique "@query" in
                                      (uu____27209,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27210) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27202 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))