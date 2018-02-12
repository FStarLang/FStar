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
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____5745),uu____5746) ->
           let uu____5795 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____5803 -> false in
           if uu____5795
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____5819;
              FStar_Syntax_Syntax.vars = uu____5820;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____5837 = varops.fresh "t" in
             (uu____5837, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____5840 =
               let uu____5851 =
                 let uu____5854 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____5854 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____5851) in
             FStar_SMTEncoding_Term.DeclFun uu____5840 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5862) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5872 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____5872, [])
       | FStar_Syntax_Syntax.Tm_type uu____5875 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5879) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____5904 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____5904 with
            | (binders1,res) ->
                let uu____5915 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____5915
                then
                  let uu____5920 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____5920 with
                   | (vars,guards,env',decls,uu____5945) ->
                       let fsym =
                         let uu____5963 = varops.fresh "f" in
                         (uu____5963, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____5966 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___111_5975 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___111_5975.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___111_5975.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___111_5975.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___111_5975.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___111_5975.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___111_5975.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___111_5975.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___111_5975.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___111_5975.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___111_5975.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___111_5975.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___111_5975.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___111_5975.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___111_5975.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___111_5975.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___111_5975.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___111_5975.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___111_5975.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___111_5975.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___111_5975.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___111_5975.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___111_5975.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___111_5975.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___111_5975.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___111_5975.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___111_5975.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___111_5975.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___111_5975.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___111_5975.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___111_5975.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___111_5975.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___111_5975.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___111_5975.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___111_5975.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____5966 with
                        | (pre_opt,res_t) ->
                            let uu____5986 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____5986 with
                             | (res_pred,decls') ->
                                 let uu____5997 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6010 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6010, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6014 =
                                         encode_formula pre env' in
                                       (match uu____6014 with
                                        | (guard,decls0) ->
                                            let uu____6027 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6027, decls0)) in
                                 (match uu____5997 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6039 =
                                          let uu____6050 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6050) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6039 in
                                      let cvars =
                                        let uu____6068 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6068
                                          (FStar_List.filter
                                             (fun uu____6082  ->
                                                match uu____6082 with
                                                | (x,uu____6088) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6107 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6107 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6115 =
                                             let uu____6116 =
                                               let uu____6123 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6123) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6116 in
                                           (uu____6115,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6143 =
                                               let uu____6144 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6144 in
                                             varops.mk_unique uu____6143 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6155 =
                                               FStar_Options.log_queries () in
                                             if uu____6155
                                             then
                                               let uu____6158 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6158
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6166 =
                                               let uu____6173 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6173) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6166 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6185 =
                                               let uu____6192 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6192,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6185 in
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
                                             let uu____6213 =
                                               let uu____6220 =
                                                 let uu____6221 =
                                                   let uu____6232 =
                                                     let uu____6233 =
                                                       let uu____6238 =
                                                         let uu____6239 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6239 in
                                                       (f_has_t, uu____6238) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6233 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6232) in
                                                 mkForall_fuel uu____6221 in
                                               (uu____6220,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6213 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6262 =
                                               let uu____6269 =
                                                 let uu____6270 =
                                                   let uu____6281 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6281) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6270 in
                                               (uu____6269,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6262 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6306 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6306);
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
                     let uu____6321 =
                       let uu____6328 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6328,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6321 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6340 =
                       let uu____6347 =
                         let uu____6348 =
                           let uu____6359 =
                             let uu____6360 =
                               let uu____6365 =
                                 let uu____6366 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6366 in
                               (f_has_t, uu____6365) in
                             FStar_SMTEncoding_Util.mkImp uu____6360 in
                           ([[f_has_t]], [fsym], uu____6359) in
                         mkForall_fuel uu____6348 in
                       (uu____6347, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6340 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6393 ->
           let uu____6400 =
             let uu____6405 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6405 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6412;
                 FStar_Syntax_Syntax.vars = uu____6413;_} ->
                 let uu____6420 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6420 with
                  | (b,f1) ->
                      let uu____6445 =
                        let uu____6446 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6446 in
                      (uu____6445, f1))
             | uu____6455 -> failwith "impossible" in
           (match uu____6400 with
            | (x,f) ->
                let uu____6466 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6466 with
                 | (base_t,decls) ->
                     let uu____6477 = gen_term_var env x in
                     (match uu____6477 with
                      | (x1,xtm,env') ->
                          let uu____6491 = encode_formula f env' in
                          (match uu____6491 with
                           | (refinement,decls') ->
                               let uu____6502 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6502 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6518 =
                                        let uu____6521 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6528 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6521
                                          uu____6528 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6518 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6561  ->
                                              match uu____6561 with
                                              | (y,uu____6567) ->
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
                                    let uu____6600 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6600 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6608 =
                                           let uu____6609 =
                                             let uu____6616 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6616) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6609 in
                                         (uu____6608,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6637 =
                                             let uu____6638 =
                                               let uu____6639 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6639 in
                                             Prims.strcat module_name
                                               uu____6638 in
                                           varops.mk_unique uu____6637 in
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
                                           let uu____6653 =
                                             let uu____6660 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6660) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6653 in
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
                                           let uu____6675 =
                                             let uu____6682 =
                                               let uu____6683 =
                                                 let uu____6694 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6694) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6683 in
                                             (uu____6682,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6675 in
                                         let t_kinding =
                                           let uu____6712 =
                                             let uu____6719 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6719,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6712 in
                                         let t_interp =
                                           let uu____6737 =
                                             let uu____6744 =
                                               let uu____6745 =
                                                 let uu____6756 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6756) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6745 in
                                             let uu____6779 =
                                               let uu____6782 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6782 in
                                             (uu____6744, uu____6779,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6737 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____6789 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6789);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6819 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6819 in
           let uu____6820 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____6820 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6832 =
                    let uu____6839 =
                      let uu____6840 =
                        let uu____6841 =
                          let uu____6842 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6842 in
                        FStar_Util.format1 "uvar_typing_%s" uu____6841 in
                      varops.mk_unique uu____6840 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6839) in
                  FStar_SMTEncoding_Util.mkAssume uu____6832 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6847 ->
           let uu____6862 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____6862 with
            | (head1,args_e) ->
                let uu____6903 =
                  let uu____6916 =
                    let uu____6917 = FStar_Syntax_Subst.compress head1 in
                    uu____6917.FStar_Syntax_Syntax.n in
                  (uu____6916, args_e) in
                (match uu____6903 with
                 | uu____6932 when head_redex env head1 ->
                     let uu____6945 = whnf env t in
                     encode_term uu____6945 env
                 | uu____6946 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6965 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6979;
                       FStar_Syntax_Syntax.vars = uu____6980;_},uu____6981),uu____6982::
                    (v1,uu____6984)::(v2,uu____6986)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7037 = encode_term v1 env in
                     (match uu____7037 with
                      | (v11,decls1) ->
                          let uu____7048 = encode_term v2 env in
                          (match uu____7048 with
                           | (v21,decls2) ->
                               let uu____7059 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7059,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7063::(v1,uu____7065)::(v2,uu____7067)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7114 = encode_term v1 env in
                     (match uu____7114 with
                      | (v11,decls1) ->
                          let uu____7125 = encode_term v2 env in
                          (match uu____7125 with
                           | (v21,decls2) ->
                               let uu____7136 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7136,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7140)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7166)::(rng,uu____7168)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7203) ->
                     let e0 =
                       let uu____7221 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7221 in
                     ((let uu____7229 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7229
                       then
                         let uu____7230 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7230
                       else ());
                      (let e =
                         let uu____7235 =
                           let uu____7236 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7237 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7236
                             uu____7237 in
                         uu____7235 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7246),(arg,uu____7248)::[]) -> encode_term arg env
                 | uu____7273 ->
                     let uu____7286 = encode_args args_e env in
                     (match uu____7286 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7341 = encode_term head1 env in
                            match uu____7341 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7405 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7405 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7483  ->
                                                 fun uu____7484  ->
                                                   match (uu____7483,
                                                           uu____7484)
                                                   with
                                                   | ((bv,uu____7506),
                                                      (a,uu____7508)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7526 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7526
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7531 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7531 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7546 =
                                                   let uu____7553 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7562 =
                                                     let uu____7563 =
                                                       let uu____7564 =
                                                         let uu____7565 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7565 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7564 in
                                                     varops.mk_unique
                                                       uu____7563 in
                                                   (uu____7553,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7562) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7546 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7582 = lookup_free_var_sym env fv in
                            match uu____7582 with
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
                                   FStar_Syntax_Syntax.pos = uu____7613;
                                   FStar_Syntax_Syntax.vars = uu____7614;_},uu____7615)
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
                                   FStar_Syntax_Syntax.pos = uu____7626;
                                   FStar_Syntax_Syntax.vars = uu____7627;_},uu____7628)
                                ->
                                let uu____7633 =
                                  let uu____7634 =
                                    let uu____7639 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7639
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7634
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7633
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7669 =
                                  let uu____7670 =
                                    let uu____7675 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7675
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7670
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7669
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7704,(FStar_Util.Inl t1,uu____7706),uu____7707)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7756,(FStar_Util.Inr c,uu____7758),uu____7759)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7808 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7835 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7835 in
                               let uu____7836 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____7836 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7852;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7853;_},uu____7854)
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
                                     | uu____7868 ->
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
           let uu____7917 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____7917 with
            | (bs1,body1,opening) ->
                let fallback uu____7940 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____7947 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____7947, [decl]) in
                let is_impure rc =
                  let uu____7954 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____7954 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7964 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____7964
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____7984 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____7984
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____7988 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____7988)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7995 =
                         let uu____8000 =
                           let uu____8001 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8001 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8000) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7995);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8003 =
                       (is_impure rc) &&
                         (let uu____8005 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8005) in
                     if uu____8003
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8012 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8012 with
                        | (vars,guards,envbody,decls,uu____8037) ->
                            let body2 =
                              let uu____8051 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8051
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8053 = encode_term body2 envbody in
                            (match uu____8053 with
                             | (body3,decls') ->
                                 let uu____8064 =
                                   let uu____8073 = codomain_eff rc in
                                   match uu____8073 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8092 = encode_term tfun env in
                                       (match uu____8092 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8064 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8124 =
                                          let uu____8135 =
                                            let uu____8136 =
                                              let uu____8141 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8141, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8136 in
                                          ([], vars, uu____8135) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8124 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8153 =
                                              let uu____8156 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8156
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8153 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8175 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8175 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8183 =
                                             let uu____8184 =
                                               let uu____8191 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8191) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8184 in
                                           (uu____8183,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8202 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8202 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8213 =
                                                    let uu____8214 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8214 = cache_size in
                                                  if uu____8213
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
                                                    let uu____8230 =
                                                      let uu____8231 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8231 in
                                                    varops.mk_unique
                                                      uu____8230 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8238 =
                                                    let uu____8245 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8245) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8238 in
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
                                                      let uu____8263 =
                                                        let uu____8264 =
                                                          let uu____8271 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8271,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8264 in
                                                      [uu____8263] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8284 =
                                                    let uu____8291 =
                                                      let uu____8292 =
                                                        let uu____8303 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8303) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8292 in
                                                    (uu____8291,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8284 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8320 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8320);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8323,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8324;
                          FStar_Syntax_Syntax.lbunivs = uu____8325;
                          FStar_Syntax_Syntax.lbtyp = uu____8326;
                          FStar_Syntax_Syntax.lbeff = uu____8327;
                          FStar_Syntax_Syntax.lbdef = uu____8328;
                          FStar_Syntax_Syntax.lbattrs = uu____8329;_}::uu____8330),uu____8331)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8361;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8363;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8365;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8389 ->
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
              let uu____8459 =
                let uu____8464 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu____8464 env in
              match uu____8459 with
              | (ee1,decls1) ->
                  let uu____8485 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8485 with
                   | (xs,e21) ->
                       let uu____8510 = FStar_List.hd xs in
                       (match uu____8510 with
                        | (x1,uu____8524) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8526 = encode_body e21 env' in
                            (match uu____8526 with
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
            let uu____8558 =
              let uu____8565 =
                let uu____8566 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8566 in
              gen_term_var env uu____8565 in
            match uu____8558 with
            | (scrsym,scr',env1) ->
                let uu____8574 = encode_term e env1 in
                (match uu____8574 with
                 | (scr,decls) ->
                     let uu____8585 =
                       let encode_branch b uu____8610 =
                         match uu____8610 with
                         | (else_case,decls1) ->
                             let uu____8629 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8629 with
                              | (p,w,br) ->
                                  let uu____8655 = encode_pat env1 p in
                                  (match uu____8655 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8692  ->
                                                   match uu____8692 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8699 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8721 =
                                               encode_term w1 env2 in
                                             (match uu____8721 with
                                              | (w2,decls2) ->
                                                  let uu____8734 =
                                                    let uu____8735 =
                                                      let uu____8740 =
                                                        let uu____8741 =
                                                          let uu____8746 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8746) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8741 in
                                                      (guard, uu____8740) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8735 in
                                                  (uu____8734, decls2)) in
                                       (match uu____8699 with
                                        | (guard1,decls2) ->
                                            let uu____8759 =
                                              encode_br br env2 in
                                            (match uu____8759 with
                                             | (br1,decls3) ->
                                                 let uu____8772 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8772,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8585 with
                      | (match_tm,decls1) ->
                          let uu____8791 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____8791, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____8831 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____8831
       then
         let uu____8832 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8832
       else ());
      (let uu____8834 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____8834 with
       | (vars,pat_term) ->
           let uu____8851 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8904  ->
                     fun v1  ->
                       match uu____8904 with
                       | (env1,vars1) ->
                           let uu____8956 = gen_term_var env1 v1 in
                           (match uu____8956 with
                            | (xx,uu____8978,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____8851 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9057 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9058 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9059 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9067 = encode_const c env1 in
                      (match uu____9067 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9081::uu____9082 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9085 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9108 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9108 with
                        | (uu____9115,uu____9116::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9119 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9152  ->
                                  match uu____9152 with
                                  | (arg,uu____9160) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9166 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9166)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9193) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9224 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9247 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9291  ->
                                  match uu____9291 with
                                  | (arg,uu____9305) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9311 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9311)) in
                      FStar_All.pipe_right uu____9247 FStar_List.flatten in
                let pat_term1 uu____9339 = encode_term pat_term env1 in
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
      let uu____9349 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9387  ->
                fun uu____9388  ->
                  match (uu____9387, uu____9388) with
                  | ((tms,decls),(t,uu____9424)) ->
                      let uu____9445 = encode_term t env in
                      (match uu____9445 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9349 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9502 = FStar_Syntax_Util.list_elements e in
        match uu____9502 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9523 =
          let uu____9538 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9538 FStar_Syntax_Util.head_and_args in
        match uu____9523 with
        | (head1,args) ->
            let uu____9577 =
              let uu____9590 =
                let uu____9591 = FStar_Syntax_Util.un_uinst head1 in
                uu____9591.FStar_Syntax_Syntax.n in
              (uu____9590, args) in
            (match uu____9577 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9605,uu____9606)::(e,uu____9608)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9643 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9679 =
            let uu____9694 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9694 FStar_Syntax_Util.head_and_args in
          match uu____9679 with
          | (head1,args) ->
              let uu____9735 =
                let uu____9748 =
                  let uu____9749 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9749.FStar_Syntax_Syntax.n in
                (uu____9748, args) in
              (match uu____9735 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9766)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9793 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____9815 = smt_pat_or1 t1 in
            (match uu____9815 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9831 = list_elements1 e in
                 FStar_All.pipe_right uu____9831
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9849 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____9849
                           (FStar_List.map one_pat)))
             | uu____9860 ->
                 let uu____9865 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____9865])
        | uu____9886 ->
            let uu____9889 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____9889] in
      let uu____9910 =
        let uu____9929 =
          let uu____9930 = FStar_Syntax_Subst.compress t in
          uu____9930.FStar_Syntax_Syntax.n in
        match uu____9929 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9969 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____9969 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10012;
                        FStar_Syntax_Syntax.effect_name = uu____10013;
                        FStar_Syntax_Syntax.result_typ = uu____10014;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10016)::(post,uu____10018)::(pats,uu____10020)::[];
                        FStar_Syntax_Syntax.flags = uu____10021;_}
                      ->
                      let uu____10062 = lemma_pats pats in
                      (binders1, pre, post, uu____10062)
                  | uu____10079 -> failwith "impos"))
        | uu____10098 -> failwith "Impos" in
      match uu____9910 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___112_10146 = env in
            {
              bindings = (uu___112_10146.bindings);
              depth = (uu___112_10146.depth);
              tcenv = (uu___112_10146.tcenv);
              warn = (uu___112_10146.warn);
              cache = (uu___112_10146.cache);
              nolabels = (uu___112_10146.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___112_10146.encode_non_total_function_typ);
              current_module_name = (uu___112_10146.current_module_name)
            } in
          let uu____10147 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10147 with
           | (vars,guards,env2,decls,uu____10172) ->
               let uu____10185 =
                 let uu____10200 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10254 =
                             let uu____10265 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2)) in
                             FStar_All.pipe_right uu____10265
                               FStar_List.unzip in
                           match uu____10254 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10200 FStar_List.unzip in
               (match uu____10185 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___113_10417 = env2 in
                      {
                        bindings = (uu___113_10417.bindings);
                        depth = (uu___113_10417.depth);
                        tcenv = (uu___113_10417.tcenv);
                        warn = (uu___113_10417.warn);
                        cache = (uu___113_10417.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___113_10417.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___113_10417.encode_non_total_function_typ);
                        current_module_name =
                          (uu___113_10417.current_module_name)
                      } in
                    let uu____10418 =
                      let uu____10423 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10423 env3 in
                    (match uu____10418 with
                     | (pre1,decls'') ->
                         let uu____10430 =
                           let uu____10435 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10435 env3 in
                         (match uu____10430 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10445 =
                                let uu____10446 =
                                  let uu____10457 =
                                    let uu____10458 =
                                      let uu____10463 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10463, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10458 in
                                  (pats, vars, uu____10457) in
                                FStar_SMTEncoding_Util.mkForall uu____10446 in
                              (uu____10445, decls1)))))
and encode_smt_pattern:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let uu____10476 = FStar_Syntax_Util.head_and_args t in
      match uu____10476 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1 in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10535::(x,uu____10537)::(t1,uu____10539)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10586 = encode_term x env in
               (match uu____10586 with
                | (x1,decls) ->
                    let uu____10599 = encode_term t1 env in
                    (match uu____10599 with
                     | (t2,decls') ->
                         let uu____10612 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                         (uu____10612, (FStar_List.append decls decls'))))
           | uu____10615 -> encode_term t env)
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10638 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10638
        then
          let uu____10639 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10640 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10639 uu____10640
        else () in
      let enc f r l =
        let uu____10673 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10701 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10701 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10673 with
        | (decls,args) ->
            let uu____10730 =
              let uu___114_10731 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10731.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10731.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10730, decls) in
      let const_op f r uu____10762 =
        let uu____10775 = f r in (uu____10775, []) in
      let un_op f l =
        let uu____10794 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10794 in
      let bin_op f uu___88_10810 =
        match uu___88_10810 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10821 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10855 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10878  ->
                 match uu____10878 with
                 | (t,uu____10892) ->
                     let uu____10893 = encode_formula t env in
                     (match uu____10893 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10855 with
        | (decls,phis) ->
            let uu____10922 =
              let uu___115_10923 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___115_10923.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___115_10923.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10922, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10984  ->
               match uu____10984 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11003) -> false
                    | uu____11004 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11019 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11019
        else
          (let uu____11033 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11033 r rf) in
      let mk_imp1 r uu___89_11058 =
        match uu___89_11058 with
        | (lhs,uu____11064)::(rhs,uu____11066)::[] ->
            let uu____11093 = encode_formula rhs env in
            (match uu____11093 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11108) ->
                      (l1, decls1)
                  | uu____11113 ->
                      let uu____11114 = encode_formula lhs env in
                      (match uu____11114 with
                       | (l2,decls2) ->
                           let uu____11125 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11125, (FStar_List.append decls1 decls2)))))
        | uu____11128 -> failwith "impossible" in
      let mk_ite r uu___90_11149 =
        match uu___90_11149 with
        | (guard,uu____11155)::(_then,uu____11157)::(_else,uu____11159)::[]
            ->
            let uu____11196 = encode_formula guard env in
            (match uu____11196 with
             | (g,decls1) ->
                 let uu____11207 = encode_formula _then env in
                 (match uu____11207 with
                  | (t,decls2) ->
                      let uu____11218 = encode_formula _else env in
                      (match uu____11218 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11232 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11257 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11257 in
      let connectives =
        let uu____11275 =
          let uu____11288 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11288) in
        let uu____11305 =
          let uu____11320 =
            let uu____11333 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11333) in
          let uu____11350 =
            let uu____11365 =
              let uu____11380 =
                let uu____11393 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11393) in
              let uu____11410 =
                let uu____11425 =
                  let uu____11440 =
                    let uu____11453 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11453) in
                  [uu____11440;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11425 in
              uu____11380 :: uu____11410 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11365 in
          uu____11320 :: uu____11350 in
        uu____11275 :: uu____11305 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11774 = encode_formula phi' env in
            (match uu____11774 with
             | (phi2,decls) ->
                 let uu____11785 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11785, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11786 ->
            let uu____11793 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11793 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11832 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11832 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11844;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11846;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11848;_}::[]),e2)
            ->
            let uu____11872 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11872 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11919::(x,uu____11921)::(t,uu____11923)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11970 = encode_term x env in
                 (match uu____11970 with
                  | (x1,decls) ->
                      let uu____11981 = encode_term t env in
                      (match uu____11981 with
                       | (t1,decls') ->
                           let uu____11992 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11992, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11997)::(msg,uu____11999)::(phi2,uu____12001)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12046 =
                   let uu____12051 =
                     let uu____12052 = FStar_Syntax_Subst.compress r in
                     uu____12052.FStar_Syntax_Syntax.n in
                   let uu____12055 =
                     let uu____12056 = FStar_Syntax_Subst.compress msg in
                     uu____12056.FStar_Syntax_Syntax.n in
                   (uu____12051, uu____12055) in
                 (match uu____12046 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12065))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12071 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12078)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12103 when head_redex env head2 ->
                 let uu____12116 = whnf env phi1 in
                 encode_formula uu____12116 env
             | uu____12117 ->
                 let uu____12130 = encode_term phi1 env in
                 (match uu____12130 with
                  | (tt,decls) ->
                      let uu____12141 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___116_12144 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___116_12144.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___116_12144.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12141, decls)))
        | uu____12145 ->
            let uu____12146 = encode_term phi1 env in
            (match uu____12146 with
             | (tt,decls) ->
                 let uu____12157 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___117_12160 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___117_12160.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___117_12160.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12157, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12196 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12196 with
        | (vars,guards,env2,decls,uu____12235) ->
            let uu____12248 =
              let uu____12261 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12313 =
                          let uu____12324 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12364  ->
                                    match uu____12364 with
                                    | (t,uu____12378) ->
                                        encode_smt_pattern t
                                          (let uu___118_12384 = env2 in
                                           {
                                             bindings =
                                               (uu___118_12384.bindings);
                                             depth = (uu___118_12384.depth);
                                             tcenv = (uu___118_12384.tcenv);
                                             warn = (uu___118_12384.warn);
                                             cache = (uu___118_12384.cache);
                                             nolabels =
                                               (uu___118_12384.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___118_12384.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___118_12384.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12324 FStar_List.unzip in
                        match uu____12313 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12261 FStar_List.unzip in
            (match uu____12248 with
             | (pats,decls') ->
                 let uu____12493 = encode_formula body env2 in
                 (match uu____12493 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12525;
                             FStar_SMTEncoding_Term.rng = uu____12526;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12541 -> guards in
                      let uu____12546 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12546, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12606  ->
                   match uu____12606 with
                   | (x,uu____12612) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12620 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12632 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12632) uu____12620 tl1 in
             let uu____12635 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12662  ->
                       match uu____12662 with
                       | (b,uu____12668) ->
                           let uu____12669 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12669)) in
             (match uu____12635 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12675) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12689 =
                    let uu____12694 =
                      let uu____12695 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12695 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12694) in
                  FStar_Errors.log_issue pos uu____12689) in
       let uu____12696 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12696 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12705 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12763  ->
                     match uu____12763 with
                     | (l,uu____12777) -> FStar_Ident.lid_equals op l)) in
           (match uu____12705 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12810,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12850 = encode_q_body env vars pats body in
             match uu____12850 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12895 =
                     let uu____12906 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12906) in
                   FStar_SMTEncoding_Term.mkForall uu____12895
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12925 = encode_q_body env vars pats body in
             match uu____12925 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12969 =
                   let uu____12970 =
                     let uu____12981 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12981) in
                   FStar_SMTEncoding_Term.mkExists uu____12970
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12969, decls))))
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
  let uu____13074 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13074 with
  | (asym,a) ->
      let uu____13081 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13081 with
       | (xsym,x) ->
           let uu____13088 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13088 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13132 =
                      let uu____13143 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13143, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13132 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13169 =
                      let uu____13176 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13176) in
                    FStar_SMTEncoding_Util.mkApp uu____13169 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13189 =
                    let uu____13192 =
                      let uu____13195 =
                        let uu____13198 =
                          let uu____13199 =
                            let uu____13206 =
                              let uu____13207 =
                                let uu____13218 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13218) in
                              FStar_SMTEncoding_Util.mkForall uu____13207 in
                            (uu____13206, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13199 in
                        let uu____13235 =
                          let uu____13238 =
                            let uu____13239 =
                              let uu____13246 =
                                let uu____13247 =
                                  let uu____13258 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13258) in
                                FStar_SMTEncoding_Util.mkForall uu____13247 in
                              (uu____13246,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13239 in
                          [uu____13238] in
                        uu____13198 :: uu____13235 in
                      xtok_decl :: uu____13195 in
                    xname_decl :: uu____13192 in
                  (xtok1, uu____13189) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13349 =
                    let uu____13362 =
                      let uu____13371 =
                        let uu____13372 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13372 in
                      quant axy uu____13371 in
                    (FStar_Parser_Const.op_Eq, uu____13362) in
                  let uu____13381 =
                    let uu____13396 =
                      let uu____13409 =
                        let uu____13418 =
                          let uu____13419 =
                            let uu____13420 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13420 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13419 in
                        quant axy uu____13418 in
                      (FStar_Parser_Const.op_notEq, uu____13409) in
                    let uu____13429 =
                      let uu____13444 =
                        let uu____13457 =
                          let uu____13466 =
                            let uu____13467 =
                              let uu____13468 =
                                let uu____13473 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13474 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13473, uu____13474) in
                              FStar_SMTEncoding_Util.mkLT uu____13468 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13467 in
                          quant xy uu____13466 in
                        (FStar_Parser_Const.op_LT, uu____13457) in
                      let uu____13483 =
                        let uu____13498 =
                          let uu____13511 =
                            let uu____13520 =
                              let uu____13521 =
                                let uu____13522 =
                                  let uu____13527 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13528 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13527, uu____13528) in
                                FStar_SMTEncoding_Util.mkLTE uu____13522 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13521 in
                            quant xy uu____13520 in
                          (FStar_Parser_Const.op_LTE, uu____13511) in
                        let uu____13537 =
                          let uu____13552 =
                            let uu____13565 =
                              let uu____13574 =
                                let uu____13575 =
                                  let uu____13576 =
                                    let uu____13581 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13582 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13581, uu____13582) in
                                  FStar_SMTEncoding_Util.mkGT uu____13576 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13575 in
                              quant xy uu____13574 in
                            (FStar_Parser_Const.op_GT, uu____13565) in
                          let uu____13591 =
                            let uu____13606 =
                              let uu____13619 =
                                let uu____13628 =
                                  let uu____13629 =
                                    let uu____13630 =
                                      let uu____13635 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13636 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13635, uu____13636) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13630 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13629 in
                                quant xy uu____13628 in
                              (FStar_Parser_Const.op_GTE, uu____13619) in
                            let uu____13645 =
                              let uu____13660 =
                                let uu____13673 =
                                  let uu____13682 =
                                    let uu____13683 =
                                      let uu____13684 =
                                        let uu____13689 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13690 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13689, uu____13690) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13684 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13683 in
                                  quant xy uu____13682 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13673) in
                              let uu____13699 =
                                let uu____13714 =
                                  let uu____13727 =
                                    let uu____13736 =
                                      let uu____13737 =
                                        let uu____13738 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13738 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13737 in
                                    quant qx uu____13736 in
                                  (FStar_Parser_Const.op_Minus, uu____13727) in
                                let uu____13747 =
                                  let uu____13762 =
                                    let uu____13775 =
                                      let uu____13784 =
                                        let uu____13785 =
                                          let uu____13786 =
                                            let uu____13791 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13792 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13791, uu____13792) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13786 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13785 in
                                      quant xy uu____13784 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13775) in
                                  let uu____13801 =
                                    let uu____13816 =
                                      let uu____13829 =
                                        let uu____13838 =
                                          let uu____13839 =
                                            let uu____13840 =
                                              let uu____13845 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13846 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13845, uu____13846) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13840 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13839 in
                                        quant xy uu____13838 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13829) in
                                    let uu____13855 =
                                      let uu____13870 =
                                        let uu____13883 =
                                          let uu____13892 =
                                            let uu____13893 =
                                              let uu____13894 =
                                                let uu____13899 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13900 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13899, uu____13900) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13894 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13893 in
                                          quant xy uu____13892 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13883) in
                                      let uu____13909 =
                                        let uu____13924 =
                                          let uu____13937 =
                                            let uu____13946 =
                                              let uu____13947 =
                                                let uu____13948 =
                                                  let uu____13953 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13954 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13953, uu____13954) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13948 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13947 in
                                            quant xy uu____13946 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13937) in
                                        let uu____13963 =
                                          let uu____13978 =
                                            let uu____13991 =
                                              let uu____14000 =
                                                let uu____14001 =
                                                  let uu____14002 =
                                                    let uu____14007 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14008 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14007,
                                                      uu____14008) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14002 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14001 in
                                              quant xy uu____14000 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13991) in
                                          let uu____14017 =
                                            let uu____14032 =
                                              let uu____14045 =
                                                let uu____14054 =
                                                  let uu____14055 =
                                                    let uu____14056 =
                                                      let uu____14061 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14062 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14061,
                                                        uu____14062) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14056 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14055 in
                                                quant xy uu____14054 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14045) in
                                            let uu____14071 =
                                              let uu____14086 =
                                                let uu____14099 =
                                                  let uu____14108 =
                                                    let uu____14109 =
                                                      let uu____14110 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14110 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14109 in
                                                  quant qx uu____14108 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14099) in
                                              [uu____14086] in
                                            uu____14032 :: uu____14071 in
                                          uu____13978 :: uu____14017 in
                                        uu____13924 :: uu____13963 in
                                      uu____13870 :: uu____13909 in
                                    uu____13816 :: uu____13855 in
                                  uu____13762 :: uu____13801 in
                                uu____13714 :: uu____13747 in
                              uu____13660 :: uu____13699 in
                            uu____13606 :: uu____13645 in
                          uu____13552 :: uu____13591 in
                        uu____13498 :: uu____13537 in
                      uu____13444 :: uu____13483 in
                    uu____13396 :: uu____13429 in
                  uu____13349 :: uu____13381 in
                let mk1 l v1 =
                  let uu____14324 =
                    let uu____14333 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14391  ->
                              match uu____14391 with
                              | (l',uu____14405) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14333
                      (FStar_Option.map
                         (fun uu____14465  ->
                            match uu____14465 with | (uu____14484,b) -> b v1)) in
                  FStar_All.pipe_right uu____14324 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14555  ->
                          match uu____14555 with
                          | (l',uu____14569) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14607 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14607 with
        | (xxsym,xx) ->
            let uu____14614 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14614 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14624 =
                   let uu____14631 =
                     let uu____14632 =
                       let uu____14643 =
                         let uu____14644 =
                           let uu____14649 =
                             let uu____14650 =
                               let uu____14655 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14655) in
                             FStar_SMTEncoding_Util.mkEq uu____14650 in
                           (xx_has_type, uu____14649) in
                         FStar_SMTEncoding_Util.mkImp uu____14644 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14643) in
                     FStar_SMTEncoding_Util.mkForall uu____14632 in
                   let uu____14680 =
                     let uu____14681 =
                       let uu____14682 =
                         let uu____14683 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14683 in
                       Prims.strcat module_name uu____14682 in
                     varops.mk_unique uu____14681 in
                   (uu____14631, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14680) in
                 FStar_SMTEncoding_Util.mkAssume uu____14624)
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
    let uu____14719 =
      let uu____14720 =
        let uu____14727 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14727, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14720 in
    let uu____14730 =
      let uu____14733 =
        let uu____14734 =
          let uu____14741 =
            let uu____14742 =
              let uu____14753 =
                let uu____14754 =
                  let uu____14759 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14759) in
                FStar_SMTEncoding_Util.mkImp uu____14754 in
              ([[typing_pred]], [xx], uu____14753) in
            mkForall_fuel uu____14742 in
          (uu____14741, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14734 in
      [uu____14733] in
    uu____14719 :: uu____14730 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14801 =
      let uu____14802 =
        let uu____14809 =
          let uu____14810 =
            let uu____14821 =
              let uu____14826 =
                let uu____14829 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14829] in
              [uu____14826] in
            let uu____14834 =
              let uu____14835 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14835 tt in
            (uu____14821, [bb], uu____14834) in
          FStar_SMTEncoding_Util.mkForall uu____14810 in
        (uu____14809, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14802 in
    let uu____14856 =
      let uu____14859 =
        let uu____14860 =
          let uu____14867 =
            let uu____14868 =
              let uu____14879 =
                let uu____14880 =
                  let uu____14885 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14885) in
                FStar_SMTEncoding_Util.mkImp uu____14880 in
              ([[typing_pred]], [xx], uu____14879) in
            mkForall_fuel uu____14868 in
          (uu____14867, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14860 in
      [uu____14859] in
    uu____14801 :: uu____14856 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14935 =
        let uu____14936 =
          let uu____14943 =
            let uu____14946 =
              let uu____14949 =
                let uu____14952 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14953 =
                  let uu____14956 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14956] in
                uu____14952 :: uu____14953 in
              tt :: uu____14949 in
            tt :: uu____14946 in
          ("Prims.Precedes", uu____14943) in
        FStar_SMTEncoding_Util.mkApp uu____14936 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14935 in
    let precedes_y_x =
      let uu____14960 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14960 in
    let uu____14963 =
      let uu____14964 =
        let uu____14971 =
          let uu____14972 =
            let uu____14983 =
              let uu____14988 =
                let uu____14991 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14991] in
              [uu____14988] in
            let uu____14996 =
              let uu____14997 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14997 tt in
            (uu____14983, [bb], uu____14996) in
          FStar_SMTEncoding_Util.mkForall uu____14972 in
        (uu____14971, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14964 in
    let uu____15018 =
      let uu____15021 =
        let uu____15022 =
          let uu____15029 =
            let uu____15030 =
              let uu____15041 =
                let uu____15042 =
                  let uu____15047 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15047) in
                FStar_SMTEncoding_Util.mkImp uu____15042 in
              ([[typing_pred]], [xx], uu____15041) in
            mkForall_fuel uu____15030 in
          (uu____15029, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15022 in
      let uu____15072 =
        let uu____15075 =
          let uu____15076 =
            let uu____15083 =
              let uu____15084 =
                let uu____15095 =
                  let uu____15096 =
                    let uu____15101 =
                      let uu____15102 =
                        let uu____15105 =
                          let uu____15108 =
                            let uu____15111 =
                              let uu____15112 =
                                let uu____15117 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15118 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15117, uu____15118) in
                              FStar_SMTEncoding_Util.mkGT uu____15112 in
                            let uu____15119 =
                              let uu____15122 =
                                let uu____15123 =
                                  let uu____15128 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15129 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15128, uu____15129) in
                                FStar_SMTEncoding_Util.mkGTE uu____15123 in
                              let uu____15130 =
                                let uu____15133 =
                                  let uu____15134 =
                                    let uu____15139 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15140 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15139, uu____15140) in
                                  FStar_SMTEncoding_Util.mkLT uu____15134 in
                                [uu____15133] in
                              uu____15122 :: uu____15130 in
                            uu____15111 :: uu____15119 in
                          typing_pred_y :: uu____15108 in
                        typing_pred :: uu____15105 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15102 in
                    (uu____15101, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15096 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15095) in
              mkForall_fuel uu____15084 in
            (uu____15083,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15076 in
        [uu____15075] in
      uu____15021 :: uu____15072 in
    uu____14963 :: uu____15018 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15186 =
      let uu____15187 =
        let uu____15194 =
          let uu____15195 =
            let uu____15206 =
              let uu____15211 =
                let uu____15214 = FStar_SMTEncoding_Term.boxString b in
                [uu____15214] in
              [uu____15211] in
            let uu____15219 =
              let uu____15220 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15220 tt in
            (uu____15206, [bb], uu____15219) in
          FStar_SMTEncoding_Util.mkForall uu____15195 in
        (uu____15194, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15187 in
    let uu____15241 =
      let uu____15244 =
        let uu____15245 =
          let uu____15252 =
            let uu____15253 =
              let uu____15264 =
                let uu____15265 =
                  let uu____15270 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15270) in
                FStar_SMTEncoding_Util.mkImp uu____15265 in
              ([[typing_pred]], [xx], uu____15264) in
            mkForall_fuel uu____15253 in
          (uu____15252, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15245 in
      [uu____15244] in
    uu____15186 :: uu____15241 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15323 =
      let uu____15324 =
        let uu____15331 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15331, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15324 in
    [uu____15323] in
  let mk_and_interp env conj uu____15343 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15368 =
      let uu____15369 =
        let uu____15376 =
          let uu____15377 =
            let uu____15388 =
              let uu____15389 =
                let uu____15394 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15394, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15389 in
            ([[l_and_a_b]], [aa; bb], uu____15388) in
          FStar_SMTEncoding_Util.mkForall uu____15377 in
        (uu____15376, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15369 in
    [uu____15368] in
  let mk_or_interp env disj uu____15432 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15457 =
      let uu____15458 =
        let uu____15465 =
          let uu____15466 =
            let uu____15477 =
              let uu____15478 =
                let uu____15483 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15483, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15478 in
            ([[l_or_a_b]], [aa; bb], uu____15477) in
          FStar_SMTEncoding_Util.mkForall uu____15466 in
        (uu____15465, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15458 in
    [uu____15457] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15546 =
      let uu____15547 =
        let uu____15554 =
          let uu____15555 =
            let uu____15566 =
              let uu____15567 =
                let uu____15572 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15572, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15567 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15566) in
          FStar_SMTEncoding_Util.mkForall uu____15555 in
        (uu____15554, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15547 in
    [uu____15546] in
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
    let uu____15645 =
      let uu____15646 =
        let uu____15653 =
          let uu____15654 =
            let uu____15665 =
              let uu____15666 =
                let uu____15671 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15671, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15666 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15665) in
          FStar_SMTEncoding_Util.mkForall uu____15654 in
        (uu____15653, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15646 in
    [uu____15645] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15742 =
      let uu____15743 =
        let uu____15750 =
          let uu____15751 =
            let uu____15762 =
              let uu____15763 =
                let uu____15768 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15768, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15763 in
            ([[l_imp_a_b]], [aa; bb], uu____15762) in
          FStar_SMTEncoding_Util.mkForall uu____15751 in
        (uu____15750, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15743 in
    [uu____15742] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15831 =
      let uu____15832 =
        let uu____15839 =
          let uu____15840 =
            let uu____15851 =
              let uu____15852 =
                let uu____15857 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15857, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15852 in
            ([[l_iff_a_b]], [aa; bb], uu____15851) in
          FStar_SMTEncoding_Util.mkForall uu____15840 in
        (uu____15839, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15832 in
    [uu____15831] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15909 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15909 in
    let uu____15912 =
      let uu____15913 =
        let uu____15920 =
          let uu____15921 =
            let uu____15932 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15932) in
          FStar_SMTEncoding_Util.mkForall uu____15921 in
        (uu____15920, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15913 in
    [uu____15912] in
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
      let uu____15992 =
        let uu____15999 =
          let uu____16002 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16002] in
        ("Valid", uu____15999) in
      FStar_SMTEncoding_Util.mkApp uu____15992 in
    let uu____16005 =
      let uu____16006 =
        let uu____16013 =
          let uu____16014 =
            let uu____16025 =
              let uu____16026 =
                let uu____16031 =
                  let uu____16032 =
                    let uu____16043 =
                      let uu____16048 =
                        let uu____16051 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16051] in
                      [uu____16048] in
                    let uu____16056 =
                      let uu____16057 =
                        let uu____16062 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16062, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16057 in
                    (uu____16043, [xx1], uu____16056) in
                  FStar_SMTEncoding_Util.mkForall uu____16032 in
                (uu____16031, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16026 in
            ([[l_forall_a_b]], [aa; bb], uu____16025) in
          FStar_SMTEncoding_Util.mkForall uu____16014 in
        (uu____16013, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16006 in
    [uu____16005] in
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
      let uu____16144 =
        let uu____16151 =
          let uu____16154 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16154] in
        ("Valid", uu____16151) in
      FStar_SMTEncoding_Util.mkApp uu____16144 in
    let uu____16157 =
      let uu____16158 =
        let uu____16165 =
          let uu____16166 =
            let uu____16177 =
              let uu____16178 =
                let uu____16183 =
                  let uu____16184 =
                    let uu____16195 =
                      let uu____16200 =
                        let uu____16203 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16203] in
                      [uu____16200] in
                    let uu____16208 =
                      let uu____16209 =
                        let uu____16214 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16214, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16209 in
                    (uu____16195, [xx1], uu____16208) in
                  FStar_SMTEncoding_Util.mkExists uu____16184 in
                (uu____16183, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16178 in
            ([[l_exists_a_b]], [aa; bb], uu____16177) in
          FStar_SMTEncoding_Util.mkForall uu____16166 in
        (uu____16165, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16158 in
    [uu____16157] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16274 =
      let uu____16275 =
        let uu____16282 =
          let uu____16283 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16283 range_ty in
        let uu____16284 = varops.mk_unique "typing_range_const" in
        (uu____16282, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16284) in
      FStar_SMTEncoding_Util.mkAssume uu____16275 in
    [uu____16274] in
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
        let uu____16318 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16318 x1 t in
      let uu____16319 =
        let uu____16330 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16330) in
      FStar_SMTEncoding_Util.mkForall uu____16319 in
    let uu____16353 =
      let uu____16354 =
        let uu____16361 =
          let uu____16362 =
            let uu____16373 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16373) in
          FStar_SMTEncoding_Util.mkForall uu____16362 in
        (uu____16361,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16354 in
    [uu____16353] in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e]) in
    let uu____16423 =
      let uu____16424 =
        let uu____16431 =
          let uu____16432 =
            let uu____16447 =
              let uu____16448 =
                let uu____16453 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____16454 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____16453, uu____16454) in
              FStar_SMTEncoding_Util.mkAnd uu____16448 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16447) in
          FStar_SMTEncoding_Util.mkForall' uu____16432 in
        (uu____16431,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____16424 in
    [uu____16423] in
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
          let uu____16800 =
            FStar_Util.find_opt
              (fun uu____16826  ->
                 match uu____16826 with
                 | (l,uu____16838) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16800 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16863,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16899 = encode_function_type_as_formula t env in
        match uu____16899 with
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
              let uu____16939 =
                ((let uu____16942 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16942) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16939
              then
                let uu____16949 = new_term_constant_and_tok_from_lid env lid in
                match uu____16949 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16968 =
                        let uu____16969 = FStar_Syntax_Subst.compress t_norm in
                        uu____16969.FStar_Syntax_Syntax.n in
                      match uu____16968 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16975) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17005  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17010 -> [] in
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
                (let uu____17024 = prims.is lid in
                 if uu____17024
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17032 = prims.mk lid vname in
                   match uu____17032 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17056 =
                      let uu____17067 = curried_arrow_formals_comp t_norm in
                      match uu____17067 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17085 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17085
                            then
                              let uu____17086 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___119_17089 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___119_17089.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___119_17089.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___119_17089.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___119_17089.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___119_17089.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___119_17089.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___119_17089.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___119_17089.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___119_17089.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___119_17089.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___119_17089.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___119_17089.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___119_17089.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___119_17089.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___119_17089.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___119_17089.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___119_17089.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___119_17089.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___119_17089.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___119_17089.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___119_17089.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___119_17089.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___119_17089.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___119_17089.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___119_17089.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___119_17089.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___119_17089.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___119_17089.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___119_17089.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___119_17089.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___119_17089.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___119_17089.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___119_17089.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___119_17089.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17086
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17101 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17101)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17056 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17146 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17146 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17167 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___91_17209  ->
                                       match uu___91_17209 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17213 =
                                             FStar_Util.prefix vars in
                                           (match uu____17213 with
                                            | (uu____17234,(xxsym,uu____17236))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17254 =
                                                  let uu____17255 =
                                                    let uu____17262 =
                                                      let uu____17263 =
                                                        let uu____17274 =
                                                          let uu____17275 =
                                                            let uu____17280 =
                                                              let uu____17281
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17281 in
                                                            (vapp,
                                                              uu____17280) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17275 in
                                                        ([[vapp]], vars,
                                                          uu____17274) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17263 in
                                                    (uu____17262,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17255 in
                                                [uu____17254])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17300 =
                                             FStar_Util.prefix vars in
                                           (match uu____17300 with
                                            | (uu____17321,(xxsym,uu____17323))
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
                                                let uu____17346 =
                                                  let uu____17347 =
                                                    let uu____17354 =
                                                      let uu____17355 =
                                                        let uu____17366 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17366) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17355 in
                                                    (uu____17354,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17347 in
                                                [uu____17346])
                                       | uu____17383 -> [])) in
                             let uu____17384 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17384 with
                              | (vars,guards,env',decls1,uu____17411) ->
                                  let uu____17424 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17433 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17433, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17435 =
                                          encode_formula p env' in
                                        (match uu____17435 with
                                         | (g,ds) ->
                                             let uu____17446 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17446,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17424 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17459 =
                                           let uu____17466 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17466) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17459 in
                                       let uu____17475 =
                                         let vname_decl =
                                           let uu____17483 =
                                             let uu____17494 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17504  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17494,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17483 in
                                         let uu____17513 =
                                           let env2 =
                                             let uu___120_17519 = env1 in
                                             {
                                               bindings =
                                                 (uu___120_17519.bindings);
                                               depth = (uu___120_17519.depth);
                                               tcenv = (uu___120_17519.tcenv);
                                               warn = (uu___120_17519.warn);
                                               cache = (uu___120_17519.cache);
                                               nolabels =
                                                 (uu___120_17519.nolabels);
                                               use_zfuel_name =
                                                 (uu___120_17519.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___120_17519.current_module_name)
                                             } in
                                           let uu____17520 =
                                             let uu____17521 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17521 in
                                           if uu____17520
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17513 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17536::uu____17537 ->
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
                                                     let uu____17577 =
                                                       let uu____17588 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17588) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17577 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17615 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17618 =
                                               match formals with
                                               | [] ->
                                                   let uu____17635 =
                                                     let uu____17636 =
                                                       let uu____17639 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17639 in
                                                     push_free_var env1 lid
                                                       vname uu____17636 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17635)
                                               | uu____17644 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17651 =
                                                       let uu____17658 =
                                                         let uu____17659 =
                                                           let uu____17670 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17670) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17659 in
                                                       (uu____17658,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17651 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17618 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17475 with
                                        | (decls2,env2) ->
                                            let uu____17713 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17721 =
                                                encode_term res_t1 env' in
                                              match uu____17721 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17734 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17734, decls) in
                                            (match uu____17713 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17745 =
                                                     let uu____17752 =
                                                       let uu____17753 =
                                                         let uu____17764 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17764) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17753 in
                                                     (uu____17752,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17745 in
                                                 let freshness =
                                                   let uu____17780 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17780
                                                   then
                                                     let uu____17785 =
                                                       let uu____17786 =
                                                         let uu____17797 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17808 =
                                                           varops.next_id () in
                                                         (vname, uu____17797,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17808) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17786 in
                                                     let uu____17811 =
                                                       let uu____17814 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17814] in
                                                     uu____17785 ::
                                                       uu____17811
                                                   else [] in
                                                 let g =
                                                   let uu____17819 =
                                                     let uu____17822 =
                                                       let uu____17825 =
                                                         let uu____17828 =
                                                           let uu____17831 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17831 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17828 in
                                                       FStar_List.append
                                                         decls3 uu____17825 in
                                                     FStar_List.append decls2
                                                       uu____17822 in
                                                   FStar_List.append decls11
                                                     uu____17819 in
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
          let uu____17862 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17862 with
          | FStar_Pervasives_Native.None  ->
              let uu____17899 = encode_free_var false env x t t_norm [] in
              (match uu____17899 with
               | (decls,env1) ->
                   let uu____17926 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17926 with
                    | (n1,x',uu____17953) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17974) ->
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
            let uu____18029 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18029 with
            | (decls,env1) ->
                let uu____18048 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18048
                then
                  let uu____18055 =
                    let uu____18058 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18058 in
                  (uu____18055, env1)
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
             (fun uu____18110  ->
                fun lb  ->
                  match uu____18110 with
                  | (decls,env1) ->
                      let uu____18130 =
                        let uu____18137 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18137
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18130 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18158 = FStar_Syntax_Util.head_and_args t in
    match uu____18158 with
    | (hd1,args) ->
        let uu____18195 =
          let uu____18196 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18196.FStar_Syntax_Syntax.n in
        (match uu____18195 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18200,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18219 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18241  ->
      fun quals  ->
        match uu____18241 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18317 = FStar_Util.first_N nbinders formals in
              match uu____18317 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18398  ->
                         fun uu____18399  ->
                           match (uu____18398, uu____18399) with
                           | ((formal,uu____18417),(binder,uu____18419)) ->
                               let uu____18428 =
                                 let uu____18435 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18435) in
                               FStar_Syntax_Syntax.NT uu____18428) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18443 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18474  ->
                              match uu____18474 with
                              | (x,i) ->
                                  let uu____18485 =
                                    let uu___121_18486 = x in
                                    let uu____18487 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_18486.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_18486.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18487
                                    } in
                                  (uu____18485, i))) in
                    FStar_All.pipe_right uu____18443
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18505 =
                      let uu____18506 = FStar_Syntax_Subst.compress body in
                      let uu____18507 =
                        let uu____18508 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18508 in
                      FStar_Syntax_Syntax.extend_app_n uu____18506
                        uu____18507 in
                    uu____18505 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18569 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18569
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___122_18572 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_18572.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_18572.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_18572.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_18572.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_18572.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_18572.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_18572.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_18572.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_18572.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_18572.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_18572.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_18572.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_18572.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_18572.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_18572.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_18572.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_18572.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_18572.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_18572.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___122_18572.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___122_18572.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___122_18572.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_18572.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_18572.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___122_18572.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_18572.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___122_18572.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___122_18572.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___122_18572.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_18572.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___122_18572.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___122_18572.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___122_18572.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___122_18572.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18605 = FStar_Syntax_Util.abs_formals e in
                match uu____18605 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18669::uu____18670 ->
                         let uu____18685 =
                           let uu____18686 =
                             let uu____18689 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18689 in
                           uu____18686.FStar_Syntax_Syntax.n in
                         (match uu____18685 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18732 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18732 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18774 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18774
                                   then
                                     let uu____18809 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18809 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18903  ->
                                                   fun uu____18904  ->
                                                     match (uu____18903,
                                                             uu____18904)
                                                     with
                                                     | ((x,uu____18922),
                                                        (b,uu____18924)) ->
                                                         let uu____18933 =
                                                           let uu____18940 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18940) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18933)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18942 =
                                            let uu____18963 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18963) in
                                          (uu____18942, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19031 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19031 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19120) ->
                              let uu____19125 =
                                let uu____19146 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19146 in
                              (uu____19125, true)
                          | uu____19211 when Prims.op_Negation norm1 ->
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
                          | uu____19213 ->
                              let uu____19214 =
                                let uu____19215 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19216 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19215
                                  uu____19216 in
                              failwith uu____19214)
                     | uu____19241 ->
                         let rec aux' t_norm2 =
                           let uu____19266 =
                             let uu____19267 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19267.FStar_Syntax_Syntax.n in
                           match uu____19266 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19308 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19308 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19336 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19336 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19416)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19421 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19477 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19477
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19489 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19583  ->
                            fun lb  ->
                              match uu____19583 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19678 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19678
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19681 =
                                      let uu____19696 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19696
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19681 with
                                    | (tok,decl,env2) ->
                                        let uu____19742 =
                                          let uu____19755 =
                                            let uu____19766 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19766, tok) in
                                          uu____19755 :: toks in
                                        (uu____19742, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19489 with
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
                        | uu____19949 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19957 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19957 vars)
                            else
                              (let uu____19959 =
                                 let uu____19966 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19966) in
                               FStar_SMTEncoding_Util.mkApp uu____19959) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20048;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20050;
                             FStar_Syntax_Syntax.lbeff = uu____20051;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____20053;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20119 =
                              let uu____20126 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20126 with
                              | (tcenv',uu____20144,e_t) ->
                                  let uu____20150 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20161 -> failwith "Impossible" in
                                  (match uu____20150 with
                                   | (e1,t_norm1) ->
                                       ((let uu___125_20177 = env2 in
                                         {
                                           bindings =
                                             (uu___125_20177.bindings);
                                           depth = (uu___125_20177.depth);
                                           tcenv = tcenv';
                                           warn = (uu___125_20177.warn);
                                           cache = (uu___125_20177.cache);
                                           nolabels =
                                             (uu___125_20177.nolabels);
                                           use_zfuel_name =
                                             (uu___125_20177.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___125_20177.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___125_20177.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20119 with
                             | (env',e1,t_norm1) ->
                                 let uu____20187 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20187 with
                                  | ((binders,body,uu____20208,t_body),curry)
                                      ->
                                      ((let uu____20220 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20220
                                        then
                                          let uu____20221 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20222 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20221 uu____20222
                                        else ());
                                       (let uu____20224 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20224 with
                                        | (vars,guards,env'1,binder_decls,uu____20251)
                                            ->
                                            let body1 =
                                              let uu____20265 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20265
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None) in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20282 =
                                              let uu____20291 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20291
                                              then
                                                let uu____20302 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20303 =
                                                  encode_formula body1 env'1 in
                                                (uu____20302, uu____20303)
                                              else
                                                (let uu____20313 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20313)) in
                                            (match uu____20282 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20336 =
                                                     let uu____20343 =
                                                       let uu____20344 =
                                                         let uu____20355 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20355) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20344 in
                                                     let uu____20366 =
                                                       let uu____20369 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20369 in
                                                     (uu____20343,
                                                       uu____20366,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20336 in
                                                 let uu____20372 =
                                                   let uu____20375 =
                                                     let uu____20378 =
                                                       let uu____20381 =
                                                         let uu____20384 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20384 in
                                                       FStar_List.append
                                                         decls2 uu____20381 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20378 in
                                                   FStar_List.append decls1
                                                     uu____20375 in
                                                 (uu____20372, env2))))))
                        | uu____20389 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20474 = varops.fresh "fuel" in
                          (uu____20474, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20477 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20565  ->
                                  fun uu____20566  ->
                                    match (uu____20565, uu____20566) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20714 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20714 in
                                        let gtok =
                                          let uu____20716 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20716 in
                                        let env4 =
                                          let uu____20718 =
                                            let uu____20721 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20721 in
                                          push_free_var env3 flid gtok
                                            uu____20718 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20477 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20877 t_norm
                              uu____20879 =
                              match (uu____20877, uu____20879) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20923;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20924;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;
                                                        FStar_Syntax_Syntax.lbattrs
                                                          = uu____20926;_})
                                  ->
                                  let uu____20957 =
                                    let uu____20964 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20964 with
                                    | (tcenv',uu____20986,e_t) ->
                                        let uu____20992 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21003 ->
                                              failwith "Impossible" in
                                        (match uu____20992 with
                                         | (e1,t_norm1) ->
                                             ((let uu___126_21019 = env3 in
                                               {
                                                 bindings =
                                                   (uu___126_21019.bindings);
                                                 depth =
                                                   (uu___126_21019.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___126_21019.warn);
                                                 cache =
                                                   (uu___126_21019.cache);
                                                 nolabels =
                                                   (uu___126_21019.nolabels);
                                                 use_zfuel_name =
                                                   (uu___126_21019.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___126_21019.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___126_21019.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20957 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21034 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21034
                                         then
                                           let uu____21035 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21036 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21037 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21035 uu____21036
                                             uu____21037
                                         else ());
                                        (let uu____21039 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21039 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21076 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21076
                                               then
                                                 let uu____21077 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21078 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21079 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21080 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21077 uu____21078
                                                   uu____21079 uu____21080
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21084 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21084 with
                                               | (vars,guards,env'1,binder_decls,uu____21115)
                                                   ->
                                                   let decl_g =
                                                     let uu____21129 =
                                                       let uu____21140 =
                                                         let uu____21143 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21143 in
                                                       (g, uu____21140,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21129 in
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
                                                     let uu____21168 =
                                                       let uu____21175 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21175) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21168 in
                                                   let gsapp =
                                                     let uu____21185 =
                                                       let uu____21192 =
                                                         let uu____21195 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21195 ::
                                                           vars_tm in
                                                       (g, uu____21192) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21185 in
                                                   let gmax =
                                                     let uu____21201 =
                                                       let uu____21208 =
                                                         let uu____21211 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21211 ::
                                                           vars_tm in
                                                       (g, uu____21208) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21201 in
                                                   let body1 =
                                                     let uu____21217 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21217
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21219 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21219 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21237 =
                                                            let uu____21244 =
                                                              let uu____21245
                                                                =
                                                                let uu____21260
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
                                                                  uu____21260) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21245 in
                                                            let uu____21281 =
                                                              let uu____21284
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21284 in
                                                            (uu____21244,
                                                              uu____21281,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21237 in
                                                        let eqn_f =
                                                          let uu____21288 =
                                                            let uu____21295 =
                                                              let uu____21296
                                                                =
                                                                let uu____21307
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21307) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21296 in
                                                            (uu____21295,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21288 in
                                                        let eqn_g' =
                                                          let uu____21321 =
                                                            let uu____21328 =
                                                              let uu____21329
                                                                =
                                                                let uu____21340
                                                                  =
                                                                  let uu____21341
                                                                    =
                                                                    let uu____21346
                                                                    =
                                                                    let uu____21347
                                                                    =
                                                                    let uu____21354
                                                                    =
                                                                    let uu____21357
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21357
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21354) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21347 in
                                                                    (gsapp,
                                                                    uu____21346) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21341 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21340) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21329 in
                                                            (uu____21328,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21321 in
                                                        let uu____21380 =
                                                          let uu____21389 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21389
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21418)
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
                                                                  let uu____21443
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21443
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21448
                                                                  =
                                                                  let uu____21455
                                                                    =
                                                                    let uu____21456
                                                                    =
                                                                    let uu____21467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21467) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21456 in
                                                                  (uu____21455,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21448 in
                                                              let uu____21488
                                                                =
                                                                let uu____21495
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21495
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21508
                                                                    =
                                                                    let uu____21511
                                                                    =
                                                                    let uu____21512
                                                                    =
                                                                    let uu____21519
                                                                    =
                                                                    let uu____21520
                                                                    =
                                                                    let uu____21531
                                                                    =
                                                                    let uu____21532
                                                                    =
                                                                    let uu____21537
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21537,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21532 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21531) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21520 in
                                                                    (uu____21519,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21512 in
                                                                    [uu____21511] in
                                                                    (d3,
                                                                    uu____21508) in
                                                              (match uu____21488
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21380
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
                            let uu____21602 =
                              let uu____21615 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21694  ->
                                   fun uu____21695  ->
                                     match (uu____21694, uu____21695) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21850 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21850 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21615 in
                            (match uu____21602 with
                             | (decls2,eqns,env01) ->
                                 let uu____21923 =
                                   let isDeclFun uu___92_21935 =
                                     match uu___92_21935 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21936 -> true
                                     | uu____21947 -> false in
                                   let uu____21948 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21948
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21923 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21988 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___93_21992  ->
                                 match uu___93_21992 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21993 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21999 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21999))) in
                      if uu____21988
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
                   let uu____22051 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22051
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
        let uu____22100 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22100 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22104 = encode_sigelt' env se in
      match uu____22104 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22120 =
                  let uu____22121 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22121 in
                [uu____22120]
            | uu____22122 ->
                let uu____22123 =
                  let uu____22126 =
                    let uu____22127 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22127 in
                  uu____22126 :: g in
                let uu____22128 =
                  let uu____22131 =
                    let uu____22132 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22132 in
                  [uu____22131] in
                FStar_List.append uu____22123 uu____22128 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22145 =
          let uu____22146 = FStar_Syntax_Subst.compress t in
          uu____22146.FStar_Syntax_Syntax.n in
        match uu____22145 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22150)) -> s = "opaque_to_smt"
        | uu____22151 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22156 =
          let uu____22157 = FStar_Syntax_Subst.compress t in
          uu____22157.FStar_Syntax_Syntax.n in
        match uu____22156 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22161)) -> s = "uninterpreted_by_smt"
        | uu____22162 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22167 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22172 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22175 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22178 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22193 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22197 =
            let uu____22198 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22198 Prims.op_Negation in
          if uu____22197
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22224 ->
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
               let uu____22244 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22244 with
               | (aname,atok,env2) ->
                   let uu____22260 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22260 with
                    | (formals,uu____22278) ->
                        let uu____22291 =
                          let uu____22296 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22296 env2 in
                        (match uu____22291 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22308 =
                                 let uu____22309 =
                                   let uu____22320 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22336  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22320,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22309 in
                               [uu____22308;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22349 =
                               let aux uu____22401 uu____22402 =
                                 match (uu____22401, uu____22402) with
                                 | ((bv,uu____22454),(env3,acc_sorts,acc)) ->
                                     let uu____22492 = gen_term_var env3 bv in
                                     (match uu____22492 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22349 with
                              | (uu____22564,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22587 =
                                      let uu____22594 =
                                        let uu____22595 =
                                          let uu____22606 =
                                            let uu____22607 =
                                              let uu____22612 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22612) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22607 in
                                          ([[app]], xs_sorts, uu____22606) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22595 in
                                      (uu____22594,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22587 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22632 =
                                      let uu____22639 =
                                        let uu____22640 =
                                          let uu____22651 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22651) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22640 in
                                      (uu____22639,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22632 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22670 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22670 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22698,uu____22699)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22700 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22700 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22717,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22723 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___94_22727  ->
                      match uu___94_22727 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22728 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22733 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22734 -> false)) in
            Prims.op_Negation uu____22723 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22743 =
               let uu____22750 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22750 env fv t quals in
             match uu____22743 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22765 =
                   let uu____22768 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22768 in
                 (uu____22765, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22776 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22776 with
           | (uu____22785,f1) ->
               let uu____22787 = encode_formula f1 env in
               (match uu____22787 with
                | (f2,decls) ->
                    let g =
                      let uu____22801 =
                        let uu____22802 =
                          let uu____22809 =
                            let uu____22812 =
                              let uu____22813 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22813 in
                            FStar_Pervasives_Native.Some uu____22812 in
                          let uu____22814 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22809, uu____22814) in
                        FStar_SMTEncoding_Util.mkAssume uu____22802 in
                      [uu____22801] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22820) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22832 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22850 =
                       let uu____22853 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22853.FStar_Syntax_Syntax.fv_name in
                     uu____22850.FStar_Syntax_Syntax.v in
                   let uu____22854 =
                     let uu____22855 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22855 in
                   if uu____22854
                   then
                     let val_decl =
                       let uu___129_22883 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___129_22883.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___129_22883.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___129_22883.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22888 = encode_sigelt' env1 val_decl in
                     match uu____22888 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22832 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22916,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22918;
                          FStar_Syntax_Syntax.lbtyp = uu____22919;
                          FStar_Syntax_Syntax.lbeff = uu____22920;
                          FStar_Syntax_Syntax.lbdef = uu____22921;
                          FStar_Syntax_Syntax.lbattrs = uu____22922;_}::[]),uu____22923)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22946 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22946 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22975 =
                   let uu____22978 =
                     let uu____22979 =
                       let uu____22986 =
                         let uu____22987 =
                           let uu____22998 =
                             let uu____22999 =
                               let uu____23004 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23004) in
                             FStar_SMTEncoding_Util.mkEq uu____22999 in
                           ([[b2t_x]], [xx], uu____22998) in
                         FStar_SMTEncoding_Util.mkForall uu____22987 in
                       (uu____22986,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22979 in
                   [uu____22978] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22975 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23037,uu____23038) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_23047  ->
                  match uu___95_23047 with
                  | FStar_Syntax_Syntax.Discriminator uu____23048 -> true
                  | uu____23049 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23052,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23063 =
                     let uu____23064 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23064.FStar_Ident.idText in
                   uu____23063 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___96_23068  ->
                     match uu___96_23068 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23069 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23073) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_23090  ->
                  match uu___97_23090 with
                  | FStar_Syntax_Syntax.Projector uu____23091 -> true
                  | uu____23096 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23099 = try_lookup_free_var env l in
          (match uu____23099 with
           | FStar_Pervasives_Native.Some uu____23106 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___130_23110 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___130_23110.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___130_23110.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___130_23110.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23117) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23135) ->
          let uu____23144 = encode_sigelts env ses in
          (match uu____23144 with
           | (g,env1) ->
               let uu____23161 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___98_23184  ->
                         match uu___98_23184 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23185;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23186;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23187;_}
                             -> false
                         | uu____23190 -> true)) in
               (match uu____23161 with
                | (g',inversions) ->
                    let uu____23205 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___99_23226  ->
                              match uu___99_23226 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23227 ->
                                  true
                              | uu____23238 -> false)) in
                    (match uu____23205 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23256,tps,k,uu____23259,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___100_23276  ->
                    match uu___100_23276 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23277 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23286 = c in
              match uu____23286 with
              | (name,args,uu____23291,uu____23292,uu____23293) ->
                  let uu____23298 =
                    let uu____23299 =
                      let uu____23310 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23327  ->
                                match uu____23327 with
                                | (uu____23334,sort,uu____23336) -> sort)) in
                      (name, uu____23310, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23299 in
                  [uu____23298]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23363 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23369 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23369 FStar_Option.isNone)) in
            if uu____23363
            then []
            else
              (let uu____23401 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23401 with
               | (xxsym,xx) ->
                   let uu____23410 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23449  ->
                             fun l  ->
                               match uu____23449 with
                               | (out,decls) ->
                                   let uu____23469 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23469 with
                                    | (uu____23480,data_t) ->
                                        let uu____23482 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23482 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23528 =
                                                 let uu____23529 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23529.FStar_Syntax_Syntax.n in
                                               match uu____23528 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23540,indices) ->
                                                   indices
                                               | uu____23562 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23586  ->
                                                         match uu____23586
                                                         with
                                                         | (x,uu____23592) ->
                                                             let uu____23593
                                                               =
                                                               let uu____23594
                                                                 =
                                                                 let uu____23601
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23601,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23594 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23593)
                                                    env) in
                                             let uu____23604 =
                                               encode_args indices env1 in
                                             (match uu____23604 with
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
                                                      let uu____23630 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23646
                                                                 =
                                                                 let uu____23651
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23651,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23646)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23630
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23654 =
                                                      let uu____23655 =
                                                        let uu____23660 =
                                                          let uu____23661 =
                                                            let uu____23666 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23666,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23661 in
                                                        (out, uu____23660) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23655 in
                                                    (uu____23654,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23410 with
                    | (data_ax,decls) ->
                        let uu____23679 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23679 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23690 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23690 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23694 =
                                 let uu____23701 =
                                   let uu____23702 =
                                     let uu____23713 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23728 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23713,
                                       uu____23728) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23702 in
                                 let uu____23743 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23701,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23743) in
                               FStar_SMTEncoding_Util.mkAssume uu____23694 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23746 =
            let uu____23759 =
              let uu____23760 = FStar_Syntax_Subst.compress k in
              uu____23760.FStar_Syntax_Syntax.n in
            match uu____23759 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23805 -> (tps, k) in
          (match uu____23746 with
           | (formals,res) ->
               let uu____23828 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23828 with
                | (formals1,res1) ->
                    let uu____23839 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23839 with
                     | (vars,guards,env',binder_decls,uu____23864) ->
                         let uu____23877 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23877 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23896 =
                                  let uu____23903 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23903) in
                                FStar_SMTEncoding_Util.mkApp uu____23896 in
                              let uu____23912 =
                                let tname_decl =
                                  let uu____23922 =
                                    let uu____23923 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23955  ->
                                              match uu____23955 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23968 = varops.next_id () in
                                    (tname, uu____23923,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23968, false) in
                                  constructor_or_logic_type_decl uu____23922 in
                                let uu____23977 =
                                  match vars with
                                  | [] ->
                                      let uu____23990 =
                                        let uu____23991 =
                                          let uu____23994 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23994 in
                                        push_free_var env1 t tname
                                          uu____23991 in
                                      ([], uu____23990)
                                  | uu____24001 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24010 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24010 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24024 =
                                          let uu____24031 =
                                            let uu____24032 =
                                              let uu____24047 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24047) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24032 in
                                          (uu____24031,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24024 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23977 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23912 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24087 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24087 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24105 =
                                               let uu____24106 =
                                                 let uu____24113 =
                                                   let uu____24114 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24114 in
                                                 (uu____24113,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24106 in
                                             [uu____24105]
                                           else [] in
                                         let uu____24118 =
                                           let uu____24121 =
                                             let uu____24124 =
                                               let uu____24125 =
                                                 let uu____24132 =
                                                   let uu____24133 =
                                                     let uu____24144 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24144) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24133 in
                                                 (uu____24132,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24125 in
                                             [uu____24124] in
                                           FStar_List.append karr uu____24121 in
                                         FStar_List.append decls1 uu____24118 in
                                   let aux =
                                     let uu____24160 =
                                       let uu____24163 =
                                         inversion_axioms tapp vars in
                                       let uu____24166 =
                                         let uu____24169 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24169] in
                                       FStar_List.append uu____24163
                                         uu____24166 in
                                     FStar_List.append kindingAx uu____24160 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24176,uu____24177,uu____24178,uu____24179,uu____24180)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24188,t,uu____24190,n_tps,uu____24192) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24200 = new_term_constant_and_tok_from_lid env d in
          (match uu____24200 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24217 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24217 with
                | (formals,t_res) ->
                    let uu____24252 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24252 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24266 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24266 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24336 =
                                            mk_term_projector_name d x in
                                          (uu____24336,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24338 =
                                  let uu____24357 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24357, true) in
                                FStar_All.pipe_right uu____24338
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
                              let uu____24396 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24396 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24408::uu____24409 ->
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
                                         let uu____24454 =
                                           let uu____24465 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24465) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24454
                                     | uu____24490 -> tok_typing in
                                   let uu____24499 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24499 with
                                    | (vars',guards',env'',decls_formals,uu____24524)
                                        ->
                                        let uu____24537 =
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
                                        (match uu____24537 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24568 ->
                                                   let uu____24575 =
                                                     let uu____24576 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24576 in
                                                   [uu____24575] in
                                             let encode_elim uu____24586 =
                                               let uu____24587 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24587 with
                                               | (head1,args) ->
                                                   let uu____24630 =
                                                     let uu____24631 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24631.FStar_Syntax_Syntax.n in
                                                   (match uu____24630 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24641;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24642;_},uu____24643)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24649 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24649
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
                                                                 | uu____24692
                                                                    ->
                                                                    let uu____24693
                                                                    =
                                                                    let uu____24698
                                                                    =
                                                                    let uu____24699
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24699 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24698) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24693
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24715
                                                                    =
                                                                    let uu____24716
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24716 in
                                                                    if
                                                                    uu____24715
                                                                    then
                                                                    let uu____24729
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24729]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24731
                                                               =
                                                               let uu____24744
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24794
                                                                     ->
                                                                    fun
                                                                    uu____24795
                                                                     ->
                                                                    match 
                                                                    (uu____24794,
                                                                    uu____24795)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24890
                                                                    =
                                                                    let uu____24897
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24897 in
                                                                    (match uu____24890
                                                                    with
                                                                    | 
                                                                    (uu____24910,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24918
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24918
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24920
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24920
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
                                                                 uu____24744 in
                                                             (match uu____24731
                                                              with
                                                              | (uu____24935,arg_vars,elim_eqns_or_guards,uu____24938)
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
                                                                    let uu____24968
                                                                    =
                                                                    let uu____24975
                                                                    =
                                                                    let uu____24976
                                                                    =
                                                                    let uu____24987
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24998
                                                                    =
                                                                    let uu____24999
                                                                    =
                                                                    let uu____25004
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25004) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24999 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24987,
                                                                    uu____24998) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24976 in
                                                                    (uu____24975,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24968 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25027
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25027,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25029
                                                                    =
                                                                    let uu____25036
                                                                    =
                                                                    let uu____25037
                                                                    =
                                                                    let uu____25048
                                                                    =
                                                                    let uu____25053
                                                                    =
                                                                    let uu____25056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25056] in
                                                                    [uu____25053] in
                                                                    let uu____25061
                                                                    =
                                                                    let uu____25062
                                                                    =
                                                                    let uu____25067
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25068
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25067,
                                                                    uu____25068) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25062 in
                                                                    (uu____25048,
                                                                    [x],
                                                                    uu____25061) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25037 in
                                                                    let uu____25087
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25036,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25087) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25029
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25094
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
                                                                    (let uu____25122
                                                                    =
                                                                    let uu____25123
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25123
                                                                    dapp1 in
                                                                    [uu____25122]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25094
                                                                    FStar_List.flatten in
                                                                    let uu____25130
                                                                    =
                                                                    let uu____25137
                                                                    =
                                                                    let uu____25138
                                                                    =
                                                                    let uu____25149
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25160
                                                                    =
                                                                    let uu____25161
                                                                    =
                                                                    let uu____25166
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25166) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25161 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25149,
                                                                    uu____25160) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25138 in
                                                                    (uu____25137,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25130) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25187 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25187
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
                                                                 | uu____25230
                                                                    ->
                                                                    let uu____25231
                                                                    =
                                                                    let uu____25236
                                                                    =
                                                                    let uu____25237
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25237 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25236) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25231
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25253
                                                                    =
                                                                    let uu____25254
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25254 in
                                                                    if
                                                                    uu____25253
                                                                    then
                                                                    let uu____25267
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25267]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25269
                                                               =
                                                               let uu____25282
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25332
                                                                     ->
                                                                    fun
                                                                    uu____25333
                                                                     ->
                                                                    match 
                                                                    (uu____25332,
                                                                    uu____25333)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25428
                                                                    =
                                                                    let uu____25435
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25435 in
                                                                    (match uu____25428
                                                                    with
                                                                    | 
                                                                    (uu____25448,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25456
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25456
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25458
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25458
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
                                                                 uu____25282 in
                                                             (match uu____25269
                                                              with
                                                              | (uu____25473,arg_vars,elim_eqns_or_guards,uu____25476)
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
                                                                    let uu____25506
                                                                    =
                                                                    let uu____25513
                                                                    =
                                                                    let uu____25514
                                                                    =
                                                                    let uu____25525
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25536
                                                                    =
                                                                    let uu____25537
                                                                    =
                                                                    let uu____25542
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25542) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25537 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25525,
                                                                    uu____25536) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25514 in
                                                                    (uu____25513,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25506 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25565
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25565,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25567
                                                                    =
                                                                    let uu____25574
                                                                    =
                                                                    let uu____25575
                                                                    =
                                                                    let uu____25586
                                                                    =
                                                                    let uu____25591
                                                                    =
                                                                    let uu____25594
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25594] in
                                                                    [uu____25591] in
                                                                    let uu____25599
                                                                    =
                                                                    let uu____25600
                                                                    =
                                                                    let uu____25605
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25606
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25605,
                                                                    uu____25606) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25600 in
                                                                    (uu____25586,
                                                                    [x],
                                                                    uu____25599) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25575 in
                                                                    let uu____25625
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25574,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25625) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25567
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25632
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
                                                                    (let uu____25660
                                                                    =
                                                                    let uu____25661
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25661
                                                                    dapp1 in
                                                                    [uu____25660]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25632
                                                                    FStar_List.flatten in
                                                                    let uu____25668
                                                                    =
                                                                    let uu____25675
                                                                    =
                                                                    let uu____25676
                                                                    =
                                                                    let uu____25687
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25698
                                                                    =
                                                                    let uu____25699
                                                                    =
                                                                    let uu____25704
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25704) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25699 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25687,
                                                                    uu____25698) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25676 in
                                                                    (uu____25675,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25668) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25723 ->
                                                        ((let uu____25725 =
                                                            let uu____25730 =
                                                              let uu____25731
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25732
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25731
                                                                uu____25732 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25730) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25725);
                                                         ([], []))) in
                                             let uu____25737 = encode_elim () in
                                             (match uu____25737 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25757 =
                                                      let uu____25760 =
                                                        let uu____25763 =
                                                          let uu____25766 =
                                                            let uu____25769 =
                                                              let uu____25770
                                                                =
                                                                let uu____25781
                                                                  =
                                                                  let uu____25784
                                                                    =
                                                                    let uu____25785
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25785 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25784 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25781) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25770 in
                                                            [uu____25769] in
                                                          let uu____25790 =
                                                            let uu____25793 =
                                                              let uu____25796
                                                                =
                                                                let uu____25799
                                                                  =
                                                                  let uu____25802
                                                                    =
                                                                    let uu____25805
                                                                    =
                                                                    let uu____25808
                                                                    =
                                                                    let uu____25809
                                                                    =
                                                                    let uu____25816
                                                                    =
                                                                    let uu____25817
                                                                    =
                                                                    let uu____25828
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25828) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25817 in
                                                                    (uu____25816,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25809 in
                                                                    let uu____25841
                                                                    =
                                                                    let uu____25844
                                                                    =
                                                                    let uu____25845
                                                                    =
                                                                    let uu____25852
                                                                    =
                                                                    let uu____25853
                                                                    =
                                                                    let uu____25864
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25875
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25864,
                                                                    uu____25875) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25853 in
                                                                    (uu____25852,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25845 in
                                                                    [uu____25844] in
                                                                    uu____25808
                                                                    ::
                                                                    uu____25841 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25805 in
                                                                  FStar_List.append
                                                                    uu____25802
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25799 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25796 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25793 in
                                                          FStar_List.append
                                                            uu____25766
                                                            uu____25790 in
                                                        FStar_List.append
                                                          decls3 uu____25763 in
                                                      FStar_List.append
                                                        decls2 uu____25760 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25757 in
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
           (fun uu____25921  ->
              fun se  ->
                match uu____25921 with
                | (g,env1) ->
                    let uu____25941 = encode_sigelt env1 se in
                    (match uu____25941 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25998 =
        match uu____25998 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26030 ->
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
                 ((let uu____26036 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26036
                   then
                     let uu____26037 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26038 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26039 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26037 uu____26038 uu____26039
                   else ());
                  (let uu____26041 = encode_term t1 env1 in
                   match uu____26041 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26057 =
                         let uu____26064 =
                           let uu____26065 =
                             let uu____26066 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26066
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26065 in
                         new_term_constant_from_string env1 x uu____26064 in
                       (match uu____26057 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26082 = FStar_Options.log_queries () in
                              if uu____26082
                              then
                                let uu____26085 =
                                  let uu____26086 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26087 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26088 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26086 uu____26087 uu____26088 in
                                FStar_Pervasives_Native.Some uu____26085
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26104,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26118 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26118 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26141,se,uu____26143) ->
                 let uu____26148 = encode_sigelt env1 se in
                 (match uu____26148 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26165,se) ->
                 let uu____26171 = encode_sigelt env1 se in
                 (match uu____26171 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26188 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26188 with | (uu____26211,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26223 'Auu____26224 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26224,'Auu____26223)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26292  ->
              match uu____26292 with
              | (l,uu____26304,uu____26305) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26351  ->
              match uu____26351 with
              | (l,uu____26365,uu____26366) ->
                  let uu____26375 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26376 =
                    let uu____26379 =
                      let uu____26380 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26380 in
                    [uu____26379] in
                  uu____26375 :: uu____26376)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26405 =
      let uu____26408 =
        let uu____26409 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26412 =
          let uu____26413 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26413 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26409;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26412
        } in
      [uu____26408] in
    FStar_ST.op_Colon_Equals last_env uu____26405
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26443 = FStar_ST.op_Bang last_env in
      match uu____26443 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26470 ->
          let uu___131_26473 = e in
          let uu____26474 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___131_26473.bindings);
            depth = (uu___131_26473.depth);
            tcenv;
            warn = (uu___131_26473.warn);
            cache = (uu___131_26473.cache);
            nolabels = (uu___131_26473.nolabels);
            use_zfuel_name = (uu___131_26473.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_26473.encode_non_total_function_typ);
            current_module_name = uu____26474
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26478 = FStar_ST.op_Bang last_env in
    match uu____26478 with
    | [] -> failwith "Empty env stack"
    | uu____26504::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26533  ->
    let uu____26534 = FStar_ST.op_Bang last_env in
    match uu____26534 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___132_26568 = hd1 in
          {
            bindings = (uu___132_26568.bindings);
            depth = (uu___132_26568.depth);
            tcenv = (uu___132_26568.tcenv);
            warn = (uu___132_26568.warn);
            cache = refs;
            nolabels = (uu___132_26568.nolabels);
            use_zfuel_name = (uu___132_26568.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_26568.encode_non_total_function_typ);
            current_module_name = (uu___132_26568.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26594  ->
    let uu____26595 = FStar_ST.op_Bang last_env in
    match uu____26595 with
    | [] -> failwith "Popping an empty stack"
    | uu____26621::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26685::uu____26686,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___133_26694 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___133_26694.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___133_26694.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___133_26694.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26695 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26710 =
        let uu____26713 =
          let uu____26714 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26714 in
        let uu____26715 = open_fact_db_tags env in uu____26713 :: uu____26715 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26710
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
      let uu____26737 = encode_sigelt env se in
      match uu____26737 with
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
        let uu____26773 = FStar_Options.log_queries () in
        if uu____26773
        then
          let uu____26776 =
            let uu____26777 =
              let uu____26778 =
                let uu____26779 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26779 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26778 in
            FStar_SMTEncoding_Term.Caption uu____26777 in
          uu____26776 :: decls
        else decls in
      (let uu____26790 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26790
       then
         let uu____26791 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26791
       else ());
      (let env =
         let uu____26794 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26794 tcenv in
       let uu____26795 = encode_top_level_facts env se in
       match uu____26795 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26809 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26809)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26821 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26821
       then
         let uu____26822 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26822
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26857  ->
                 fun se  ->
                   match uu____26857 with
                   | (g,env2) ->
                       let uu____26877 = encode_top_level_facts env2 se in
                       (match uu____26877 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26900 =
         encode_signature
           (let uu___134_26909 = env in
            {
              bindings = (uu___134_26909.bindings);
              depth = (uu___134_26909.depth);
              tcenv = (uu___134_26909.tcenv);
              warn = false;
              cache = (uu___134_26909.cache);
              nolabels = (uu___134_26909.nolabels);
              use_zfuel_name = (uu___134_26909.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_26909.encode_non_total_function_typ);
              current_module_name = (uu___134_26909.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26900 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26926 = FStar_Options.log_queries () in
             if uu____26926
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___135_26934 = env1 in
               {
                 bindings = (uu___135_26934.bindings);
                 depth = (uu___135_26934.depth);
                 tcenv = (uu___135_26934.tcenv);
                 warn = true;
                 cache = (uu___135_26934.cache);
                 nolabels = (uu___135_26934.nolabels);
                 use_zfuel_name = (uu___135_26934.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___135_26934.encode_non_total_function_typ);
                 current_module_name = (uu___135_26934.current_module_name)
               });
            (let uu____26936 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26936
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
        (let uu____26988 =
           let uu____26989 = FStar_TypeChecker_Env.current_module tcenv in
           uu____26989.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26988);
        (let env =
           let uu____26991 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____26991 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27003 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27038 = aux rest in
                 (match uu____27038 with
                  | (out,rest1) ->
                      let t =
                        let uu____27068 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27068 with
                        | FStar_Pervasives_Native.Some uu____27073 ->
                            let uu____27074 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27074
                              x.FStar_Syntax_Syntax.sort
                        | uu____27075 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27079 =
                        let uu____27082 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___136_27085 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_27085.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_27085.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27082 :: out in
                      (uu____27079, rest1))
             | uu____27090 -> ([], bindings1) in
           let uu____27097 = aux bindings in
           match uu____27097 with
           | (closing,bindings1) ->
               let uu____27122 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27122, bindings1) in
         match uu____27003 with
         | (q1,bindings1) ->
             let uu____27145 =
               let uu____27150 =
                 FStar_List.filter
                   (fun uu___101_27155  ->
                      match uu___101_27155 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27156 ->
                          false
                      | uu____27163 -> true) bindings1 in
               encode_env_bindings env uu____27150 in
             (match uu____27145 with
              | (env_decls,env1) ->
                  ((let uu____27181 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27181
                    then
                      let uu____27182 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27182
                    else ());
                   (let uu____27184 = encode_formula q1 env1 in
                    match uu____27184 with
                    | (phi,qdecls) ->
                        let uu____27205 =
                          let uu____27210 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27210 phi in
                        (match uu____27205 with
                         | (labels,phi1) ->
                             let uu____27227 = encode_labels labels in
                             (match uu____27227 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27264 =
                                      let uu____27271 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27272 =
                                        varops.mk_unique "@query" in
                                      (uu____27271,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27272) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27264 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))