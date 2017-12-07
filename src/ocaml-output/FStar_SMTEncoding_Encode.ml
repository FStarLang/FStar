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
      (fun uu___305_107  ->
         match uu___305_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
let subst_lcomp_opt:
  'Auu____134 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____134) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____134) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____170 =
            let uu____175 =
              let uu____176 =
                let uu____179 = l1.FStar_Syntax_Syntax.comp () in
                FStar_Syntax_Subst.subst_comp s uu____179 in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____176 in
            FStar_Util.Inl uu____175 in
          FStar_Pervasives_Native.Some uu____170
      | uu____186 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___328_205 = a in
        let uu____206 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____206;
          FStar_Syntax_Syntax.index =
            (uu___328_205.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___328_205.FStar_Syntax_Syntax.sort)
        } in
      let uu____207 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____207
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____220 =
          let uu____221 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____221 in
        let uu____222 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____222 with
        | (uu____227,t) ->
            let uu____229 =
              let uu____230 = FStar_Syntax_Subst.compress t in
              uu____230.FStar_Syntax_Syntax.n in
            (match uu____229 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____251 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____251 with
                  | (binders,uu____257) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____272 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____279 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____279
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____286 =
        let uu____291 = mk_term_projector_name lid a in
        (uu____291,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____286
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____298 =
        let uu____303 = mk_term_projector_name_by_pos lid i in
        (uu____303,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____298
let mk_data_tester:
  'Auu____308 .
    'Auu____308 ->
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
  let new_scope uu____672 =
    let uu____673 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____676 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____673, uu____676) in
  let scopes =
    let uu____696 = let uu____707 = new_scope () in [uu____707] in
    FStar_Util.mk_ref uu____696 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____748 =
        let uu____751 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____751
          (fun uu____855  ->
             match uu____855 with
             | (names1,uu____867) -> FStar_Util.smap_try_find names1 y1) in
      match uu____748 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____876 ->
          (FStar_Util.incr ctr;
           (let uu____899 =
              let uu____900 =
                let uu____901 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____901 in
              Prims.strcat "__" uu____900 in
            Prims.strcat y1 uu____899)) in
    let top_scope =
      let uu____967 =
        let uu____976 = FStar_ST.op_Bang scopes in FStar_List.hd uu____976 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____967 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1106 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1195 =
      let uu____1196 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1196 in
    FStar_Util.format2 "%s_%s" pfx uu____1195 in
  let string_const s =
    let uu____1201 =
      let uu____1204 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1204
        (fun uu____1308  ->
           match uu____1308 with
           | (uu____1319,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1201 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 () in
        let f =
          let uu____1332 = FStar_SMTEncoding_Util.mk_String_const id1 in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1332 in
        let top_scope =
          let uu____1336 =
            let uu____1345 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1345 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1336 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1464 =
    let uu____1465 =
      let uu____1476 = new_scope () in
      let uu____1485 = FStar_ST.op_Bang scopes in uu____1476 :: uu____1485 in
    FStar_ST.op_Colon_Equals scopes uu____1465 in
  let pop1 uu____1671 =
    let uu____1672 =
      let uu____1683 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1683 in
    FStar_ST.op_Colon_Equals scopes uu____1672 in
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
    let uu___329_1869 = x in
    let uu____1870 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1870;
      FStar_Syntax_Syntax.index = (uu___329_1869.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___329_1869.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1903 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1939 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____1986 'Auu____1987 .
    'Auu____1987 ->
      ('Auu____1987,'Auu____1986 FStar_Pervasives_Native.option)
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
  'Auu____2283 .
    'Auu____2283 ->
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
                 (fun uu___306_2317  ->
                    match uu___306_2317 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2321 -> [])) in
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
    let uu____2330 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___307_2340  ->
              match uu___307_2340 with
              | Binding_var (x,uu____2342) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2344,uu____2345,uu____2346) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2330 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2360 .
    env_t ->
      (binding -> 'Auu____2360 FStar_Pervasives_Native.option) ->
        'Auu____2360 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2388 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2388
      then
        let uu____2391 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2391
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
      let uu____2404 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2404)
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
        (let uu___330_2420 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___330_2420.tcenv);
           warn = (uu___330_2420.warn);
           cache = (uu___330_2420.cache);
           nolabels = (uu___330_2420.nolabels);
           use_zfuel_name = (uu___330_2420.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___330_2420.encode_non_total_function_typ);
           current_module_name = (uu___330_2420.current_module_name)
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
        (let uu___331_2438 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___331_2438.depth);
           tcenv = (uu___331_2438.tcenv);
           warn = (uu___331_2438.warn);
           cache = (uu___331_2438.cache);
           nolabels = (uu___331_2438.nolabels);
           use_zfuel_name = (uu___331_2438.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___331_2438.encode_non_total_function_typ);
           current_module_name = (uu___331_2438.current_module_name)
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
          (let uu___332_2459 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___332_2459.depth);
             tcenv = (uu___332_2459.tcenv);
             warn = (uu___332_2459.warn);
             cache = (uu___332_2459.cache);
             nolabels = (uu___332_2459.nolabels);
             use_zfuel_name = (uu___332_2459.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___332_2459.encode_non_total_function_typ);
             current_module_name = (uu___332_2459.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___333_2469 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___333_2469.depth);
          tcenv = (uu___333_2469.tcenv);
          warn = (uu___333_2469.warn);
          cache = (uu___333_2469.cache);
          nolabels = (uu___333_2469.nolabels);
          use_zfuel_name = (uu___333_2469.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___333_2469.encode_non_total_function_typ);
          current_module_name = (uu___333_2469.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___308_2493  ->
             match uu___308_2493 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2506 -> FStar_Pervasives_Native.None) in
      let uu____2511 = aux a in
      match uu____2511 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2523 = aux a2 in
          (match uu____2523 with
           | FStar_Pervasives_Native.None  ->
               let uu____2534 =
                 let uu____2535 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2536 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2535 uu____2536 in
               failwith uu____2534
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
      let uu____2563 =
        let uu___334_2564 = env in
        let uu____2565 =
          let uu____2568 =
            let uu____2569 =
              let uu____2582 =
                let uu____2585 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2585 in
              (x, fname, uu____2582, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2569 in
          uu____2568 :: (env.bindings) in
        {
          bindings = uu____2565;
          depth = (uu___334_2564.depth);
          tcenv = (uu___334_2564.tcenv);
          warn = (uu___334_2564.warn);
          cache = (uu___334_2564.cache);
          nolabels = (uu___334_2564.nolabels);
          use_zfuel_name = (uu___334_2564.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___334_2564.encode_non_total_function_typ);
          current_module_name = (uu___334_2564.current_module_name)
        } in
      (fname, ftok, uu____2563)
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
        (fun uu___309_2627  ->
           match uu___309_2627 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2666 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2683 =
        lookup_binding env
          (fun uu___310_2691  ->
             match uu___310_2691 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2706 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2683 FStar_Option.isSome
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
      let uu____2725 = try_lookup_lid env a in
      match uu____2725 with
      | FStar_Pervasives_Native.None  ->
          let uu____2758 =
            let uu____2759 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2759 in
          failwith uu____2758
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
          let uu___335_2807 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___335_2807.depth);
            tcenv = (uu___335_2807.tcenv);
            warn = (uu___335_2807.warn);
            cache = (uu___335_2807.cache);
            nolabels = (uu___335_2807.nolabels);
            use_zfuel_name = (uu___335_2807.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___335_2807.encode_non_total_function_typ);
            current_module_name = (uu___335_2807.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2821 = lookup_lid env x in
        match uu____2821 with
        | (t1,t2,uu____2834) ->
            let t3 =
              let uu____2844 =
                let uu____2851 =
                  let uu____2854 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2854] in
                (f, uu____2851) in
              FStar_SMTEncoding_Util.mkApp uu____2844 in
            let uu___336_2859 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___336_2859.depth);
              tcenv = (uu___336_2859.tcenv);
              warn = (uu___336_2859.warn);
              cache = (uu___336_2859.cache);
              nolabels = (uu___336_2859.nolabels);
              use_zfuel_name = (uu___336_2859.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___336_2859.encode_non_total_function_typ);
              current_module_name = (uu___336_2859.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2872 = try_lookup_lid env l in
      match uu____2872 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2921 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2929,fuel::[]) ->
                         let uu____2933 =
                           let uu____2934 =
                             let uu____2935 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2935
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2934 "fuel" in
                         if uu____2933
                         then
                           let uu____2938 =
                             let uu____2939 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2939
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2938
                         else FStar_Pervasives_Native.Some t
                     | uu____2943 -> FStar_Pervasives_Native.Some t)
                | uu____2944 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2957 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2957 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2961 =
            let uu____2962 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2962 in
          failwith uu____2961
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2973 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2973 with | (x,uu____2985,uu____2986) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3011 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3011 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3047;
                 FStar_SMTEncoding_Term.rng = uu____3048;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3063 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3087 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___311_3103  ->
           match uu___311_3103 with
           | Binding_fvar (uu____3106,nm',tok,uu____3109) when nm = nm' ->
               tok
           | uu____3118 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3122 .
    'Auu____3122 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3140  ->
      match uu____3140 with
      | (pats,vars,body) ->
          let fallback uu____3165 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3170 = FStar_Options.unthrottle_inductives () in
          if uu____3170
          then fallback ()
          else
            (let uu____3172 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3172 with
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
                           | uu____3203 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3224 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3224
                         | uu____3227 ->
                             let uu____3228 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3228 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3233 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3274 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3287 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3294 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3295 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3312 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3329 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3331 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3331 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3349;
             FStar_Syntax_Syntax.vars = uu____3350;_},uu____3351)
          ->
          let uu____3372 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3372 FStar_Option.isNone
      | uu____3389 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3396 =
        let uu____3397 = FStar_Syntax_Util.un_uinst t in
        uu____3397.FStar_Syntax_Syntax.n in
      match uu____3396 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3400,uu____3401,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___312_3422  ->
                  match uu___312_3422 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3423 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3425 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3425 FStar_Option.isSome
      | uu____3442 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3449 = head_normal env t in
      if uu____3449
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
    let uu____3460 =
      let uu____3461 = FStar_Syntax_Syntax.null_binder t in [uu____3461] in
    let uu____3462 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3460 uu____3462 FStar_Pervasives_Native.None
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
                    let uu____3500 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3500
                | s ->
                    let uu____3505 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3505) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___313_3520  ->
    match uu___313_3520 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3521 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3557;
                       FStar_SMTEncoding_Term.rng = uu____3558;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3581) ->
              let uu____3590 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3601 -> false) args (FStar_List.rev xs)) in
              if uu____3590
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3605,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3609 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3613 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3613)) in
              if uu____3609
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3617 -> FStar_Pervasives_Native.None in
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
    | uu____3839 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3843 -> false
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3862 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3875 ->
            let uu____3882 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3882
        | uu____3883 ->
            if norm1
            then let uu____3884 = whnf env t1 in aux false uu____3884
            else
              (let uu____3886 =
                 let uu____3887 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3888 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3887 uu____3888 in
               failwith uu____3886) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3920) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3925 ->
        let uu____3926 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3926)
let is_arithmetic_primitive:
  'Auu____3940 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3940 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3960::uu____3961::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3965::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3968 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3989 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4004 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4008 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4008)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4047)::uu____4048::uu____4049::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4100)::uu____4101::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4138 -> false
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
          let uu____4345 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4345, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4348 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4348, [])
      | FStar_Const.Const_char c1 ->
          let uu____4352 =
            let uu____4353 =
              let uu____4360 =
                let uu____4363 =
                  let uu____4364 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4364 in
                [uu____4363] in
              ("FStar.Char.__char_of_int", uu____4360) in
            FStar_SMTEncoding_Util.mkApp uu____4353 in
          (uu____4352, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4380 =
            let uu____4381 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4381 in
          (uu____4380, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4402) ->
          let uu____4403 = varops.string_const s in (uu____4403, [])
      | FStar_Const.Const_range uu____4406 ->
          let uu____4407 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4407, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4413 =
            let uu____4414 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4414 in
          failwith uu____4413
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
        (let uu____4443 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4443
         then
           let uu____4444 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4444
         else ());
        (let uu____4446 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4530  ->
                   fun b  ->
                     match uu____4530 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4609 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4625 = gen_term_var env1 x in
                           match uu____4625 with
                           | (xxsym,xx,env') ->
                               let uu____4649 =
                                 let uu____4654 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4654 env1 xx in
                               (match uu____4649 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4609 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4446 with
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
          let uu____4813 = encode_term t env in
          match uu____4813 with
          | (t1,decls) ->
              let uu____4824 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4824, decls)
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
          let uu____4835 = encode_term t env in
          match uu____4835 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4850 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4850, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4852 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4852, decls))
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
        let uu____4858 = encode_args args_e env in
        match uu____4858 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4877 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4886 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4886 in
            let binary arg_tms1 =
              let uu____4899 =
                let uu____4900 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4900 in
              let uu____4901 =
                let uu____4902 =
                  let uu____4903 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4903 in
                FStar_SMTEncoding_Term.unboxInt uu____4902 in
              (uu____4899, uu____4901) in
            let mk_default uu____4909 =
              let uu____4910 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4910 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4961 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4961
              then
                let uu____4962 = let uu____4963 = mk_args ts in op uu____4963 in
                FStar_All.pipe_right uu____4962 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4992 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4992
              then
                let uu____4993 = binary ts in
                match uu____4993 with
                | (t1,t2) ->
                    let uu____5000 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5000
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5004 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5004
                 then
                   let uu____5005 = op (binary ts) in
                   FStar_All.pipe_right uu____5005
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
            let uu____5136 =
              let uu____5145 =
                FStar_List.tryFind
                  (fun uu____5167  ->
                     match uu____5167 with
                     | (l,uu____5177) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5145 FStar_Util.must in
            (match uu____5136 with
             | (uu____5216,op) ->
                 let uu____5226 = op arg_tms in (uu____5226, decls))
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
        let uu____5234 = FStar_List.hd args_e in
        match uu____5234 with
        | (tm_sz,uu____5242) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5252 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5252 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5260 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5260);
                   t_decls) in
            let uu____5261 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5281::(sz_arg,uu____5283)::uu____5284::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5333 =
                    let uu____5336 = FStar_List.tail args_e in
                    FStar_List.tail uu____5336 in
                  let uu____5339 =
                    let uu____5342 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5342 in
                  (uu____5333, uu____5339)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5348::(sz_arg,uu____5350)::uu____5351::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5400 =
                    let uu____5401 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5401 in
                  failwith uu____5400
              | uu____5410 ->
                  let uu____5417 = FStar_List.tail args_e in
                  (uu____5417, FStar_Pervasives_Native.None) in
            (match uu____5261 with
             | (arg_tms,ext_sz) ->
                 let uu____5440 = encode_args arg_tms env in
                 (match uu____5440 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5461 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5470 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5470 in
                      let unary_arith arg_tms2 =
                        let uu____5479 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5479 in
                      let binary arg_tms2 =
                        let uu____5492 =
                          let uu____5493 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5493 in
                        let uu____5494 =
                          let uu____5495 =
                            let uu____5496 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5496 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5495 in
                        (uu____5492, uu____5494) in
                      let binary_arith arg_tms2 =
                        let uu____5511 =
                          let uu____5512 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5512 in
                        let uu____5513 =
                          let uu____5514 =
                            let uu____5515 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5515 in
                          FStar_SMTEncoding_Term.unboxInt uu____5514 in
                        (uu____5511, uu____5513) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5564 =
                          let uu____5565 = mk_args ts in op uu____5565 in
                        FStar_All.pipe_right uu____5564 resBox in
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
                        let uu____5673 =
                          let uu____5676 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5676 in
                        let uu____5678 =
                          let uu____5681 =
                            let uu____5682 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5682 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5681 in
                        mk_bv uu____5673 unary uu____5678 arg_tms2 in
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
                      let uu____5881 =
                        let uu____5890 =
                          FStar_List.tryFind
                            (fun uu____5912  ->
                               match uu____5912 with
                               | (l,uu____5922) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5890 FStar_Util.must in
                      (match uu____5881 with
                       | (uu____5963,op) ->
                           let uu____5973 = op arg_tms1 in
                           (uu____5973, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5984 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5984
       then
         let uu____5985 = FStar_Syntax_Print.tag_of_term t in
         let uu____5986 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5987 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5985 uu____5986
           uu____5987
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5993 ->
           let uu____6018 =
             let uu____6019 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6020 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6021 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6022 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6019
               uu____6020 uu____6021 uu____6022 in
           failwith uu____6018
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6027 =
             let uu____6028 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6029 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6030 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6031 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6028
               uu____6029 uu____6030 uu____6031 in
           failwith uu____6027
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6037 =
             let uu____6038 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6038 in
           failwith uu____6037
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6045) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6086;
              FStar_Syntax_Syntax.vars = uu____6087;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6104 = varops.fresh "t" in
             (uu____6104, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6107 =
               let uu____6118 =
                 let uu____6121 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6121 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6118) in
             FStar_SMTEncoding_Term.DeclFun uu____6107 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6129) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6139 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6139, [])
       | FStar_Syntax_Syntax.Tm_type uu____6142 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6146) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6171 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6171 with
            | (binders1,res) ->
                let uu____6182 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6182
                then
                  let uu____6187 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6187 with
                   | (vars,guards,env',decls,uu____6212) ->
                       let fsym =
                         let uu____6230 = varops.fresh "f" in
                         (uu____6230, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6233 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___337_6242 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___337_6242.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___337_6242.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___337_6242.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___337_6242.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___337_6242.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___337_6242.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___337_6242.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___337_6242.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___337_6242.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___337_6242.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___337_6242.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___337_6242.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___337_6242.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___337_6242.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___337_6242.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___337_6242.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___337_6242.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___337_6242.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___337_6242.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___337_6242.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___337_6242.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___337_6242.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___337_6242.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___337_6242.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___337_6242.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___337_6242.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___337_6242.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___337_6242.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___337_6242.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___337_6242.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___337_6242.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___337_6242.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___337_6242.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6233 with
                        | (pre_opt,res_t) ->
                            let uu____6253 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6253 with
                             | (res_pred,decls') ->
                                 let uu____6264 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6277 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6277, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6281 =
                                         encode_formula pre env' in
                                       (match uu____6281 with
                                        | (guard,decls0) ->
                                            let uu____6294 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6294, decls0)) in
                                 (match uu____6264 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6306 =
                                          let uu____6317 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6317) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6306 in
                                      let cvars =
                                        let uu____6335 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6335
                                          (FStar_List.filter
                                             (fun uu____6349  ->
                                                match uu____6349 with
                                                | (x,uu____6355) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6374 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6374 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6382 =
                                             let uu____6383 =
                                               let uu____6390 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6390) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6383 in
                                           (uu____6382,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6410 =
                                               let uu____6411 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6411 in
                                             varops.mk_unique uu____6410 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6422 =
                                               FStar_Options.log_queries () in
                                             if uu____6422
                                             then
                                               let uu____6425 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6425
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6433 =
                                               let uu____6440 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6440) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6433 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6452 =
                                               let uu____6459 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6459,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6452 in
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
                                             let uu____6480 =
                                               let uu____6487 =
                                                 let uu____6488 =
                                                   let uu____6499 =
                                                     let uu____6500 =
                                                       let uu____6505 =
                                                         let uu____6506 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6506 in
                                                       (f_has_t, uu____6505) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6500 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6499) in
                                                 mkForall_fuel uu____6488 in
                                               (uu____6487,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6480 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6529 =
                                               let uu____6536 =
                                                 let uu____6537 =
                                                   let uu____6548 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6548) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6537 in
                                               (uu____6536,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6529 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6573 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6573);
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
                     let uu____6588 =
                       let uu____6595 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6595,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6588 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6607 =
                       let uu____6614 =
                         let uu____6615 =
                           let uu____6626 =
                             let uu____6627 =
                               let uu____6632 =
                                 let uu____6633 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6633 in
                               (f_has_t, uu____6632) in
                             FStar_SMTEncoding_Util.mkImp uu____6627 in
                           ([[f_has_t]], [fsym], uu____6626) in
                         mkForall_fuel uu____6615 in
                       (uu____6614, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6607 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6660 ->
           let uu____6667 =
             let uu____6672 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6672 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6679;
                 FStar_Syntax_Syntax.vars = uu____6680;_} ->
                 let uu____6687 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6687 with
                  | (b,f1) ->
                      let uu____6712 =
                        let uu____6713 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6713 in
                      (uu____6712, f1))
             | uu____6722 -> failwith "impossible" in
           (match uu____6667 with
            | (x,f) ->
                let uu____6733 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6733 with
                 | (base_t,decls) ->
                     let uu____6744 = gen_term_var env x in
                     (match uu____6744 with
                      | (x1,xtm,env') ->
                          let uu____6758 = encode_formula f env' in
                          (match uu____6758 with
                           | (refinement,decls') ->
                               let uu____6769 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6769 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6785 =
                                        let uu____6788 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6795 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6788
                                          uu____6795 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6785 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6828  ->
                                              match uu____6828 with
                                              | (y,uu____6834) ->
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
                                    let uu____6867 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6867 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6875 =
                                           let uu____6876 =
                                             let uu____6883 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6883) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6876 in
                                         (uu____6875,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6904 =
                                             let uu____6905 =
                                               let uu____6906 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6906 in
                                             Prims.strcat module_name
                                               uu____6905 in
                                           varops.mk_unique uu____6904 in
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
                                           let uu____6920 =
                                             let uu____6927 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6927) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6920 in
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
                                           let uu____6942 =
                                             let uu____6949 =
                                               let uu____6950 =
                                                 let uu____6961 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6961) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6950 in
                                             (uu____6949,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6942 in
                                         let t_kinding =
                                           let uu____6979 =
                                             let uu____6986 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6986,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6979 in
                                         let t_interp =
                                           let uu____7004 =
                                             let uu____7011 =
                                               let uu____7012 =
                                                 let uu____7023 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7023) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7012 in
                                             let uu____7046 =
                                               let uu____7049 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7049 in
                                             (uu____7011, uu____7046,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7004 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7056 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7056);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7086 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7086 in
           let uu____7087 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7087 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7099 =
                    let uu____7106 =
                      let uu____7107 =
                        let uu____7108 =
                          let uu____7109 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7109 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7108 in
                      varops.mk_unique uu____7107 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7106) in
                  FStar_SMTEncoding_Util.mkAssume uu____7099 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7114 ->
           let uu____7129 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7129 with
            | (head1,args_e) ->
                let uu____7170 =
                  let uu____7183 =
                    let uu____7184 = FStar_Syntax_Subst.compress head1 in
                    uu____7184.FStar_Syntax_Syntax.n in
                  (uu____7183, args_e) in
                (match uu____7170 with
                 | uu____7199 when head_redex env head1 ->
                     let uu____7212 = whnf env t in
                     encode_term uu____7212 env
                 | uu____7213 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7232 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7246;
                       FStar_Syntax_Syntax.vars = uu____7247;_},uu____7248),uu____7249::
                    (v1,uu____7251)::(v2,uu____7253)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7304 = encode_term v1 env in
                     (match uu____7304 with
                      | (v11,decls1) ->
                          let uu____7315 = encode_term v2 env in
                          (match uu____7315 with
                           | (v21,decls2) ->
                               let uu____7326 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7326,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7330::(v1,uu____7332)::(v2,uu____7334)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7381 = encode_term v1 env in
                     (match uu____7381 with
                      | (v11,decls1) ->
                          let uu____7392 = encode_term v2 env in
                          (match uu____7392 with
                           | (v21,decls2) ->
                               let uu____7403 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7403,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7407)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7433)::(arg,uu____7435)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7470) ->
                     let e0 =
                       let uu____7488 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7488 in
                     ((let uu____7496 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7496
                       then
                         let uu____7497 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7497
                       else ());
                      (let e =
                         let uu____7502 =
                           let uu____7503 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7504 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7503
                             uu____7504 in
                         uu____7502 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7513),(arg,uu____7515)::[]) -> encode_term arg env
                 | uu____7540 ->
                     let uu____7553 = encode_args args_e env in
                     (match uu____7553 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7608 = encode_term head1 env in
                            match uu____7608 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7672 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7672 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7750  ->
                                                 fun uu____7751  ->
                                                   match (uu____7750,
                                                           uu____7751)
                                                   with
                                                   | ((bv,uu____7773),
                                                      (a,uu____7775)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7793 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7793
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7798 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7798 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7813 =
                                                   let uu____7820 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7829 =
                                                     let uu____7830 =
                                                       let uu____7831 =
                                                         let uu____7832 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7832 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7831 in
                                                     varops.mk_unique
                                                       uu____7830 in
                                                   (uu____7820,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7829) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7813 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7849 = lookup_free_var_sym env fv in
                            match uu____7849 with
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
                                   FStar_Syntax_Syntax.pos = uu____7880;
                                   FStar_Syntax_Syntax.vars = uu____7881;_},uu____7882)
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
                                   FStar_Syntax_Syntax.pos = uu____7893;
                                   FStar_Syntax_Syntax.vars = uu____7894;_},uu____7895)
                                ->
                                let uu____7900 =
                                  let uu____7901 =
                                    let uu____7906 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7906
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7901
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7900
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7936 =
                                  let uu____7937 =
                                    let uu____7942 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7942
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7937
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7936
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7971,(FStar_Util.Inl t1,uu____7973),uu____7974)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8023,(FStar_Util.Inr c,uu____8025),uu____8026)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8075 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8102 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8102 in
                               let uu____8103 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8103 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8119;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8120;_},uu____8121)
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
                                     | uu____8135 ->
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
           let uu____8184 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8184 with
            | (bs1,body1,opening) ->
                let fallback uu____8207 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8214 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8214, [decl]) in
                let is_impure rc =
                  let uu____8221 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8221 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8231 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8231
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8251 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8251
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8255 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8255)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8262 =
                         let uu____8267 =
                           let uu____8268 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8268 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8267) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8262);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8270 =
                       (is_impure rc) &&
                         (let uu____8272 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8272) in
                     if uu____8270
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8279 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8279 with
                        | (vars,guards,envbody,decls,uu____8304) ->
                            let body2 =
                              let uu____8318 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8318
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8320 = encode_term body2 envbody in
                            (match uu____8320 with
                             | (body3,decls') ->
                                 let uu____8331 =
                                   let uu____8340 = codomain_eff rc in
                                   match uu____8340 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8359 = encode_term tfun env in
                                       (match uu____8359 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8331 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8391 =
                                          let uu____8402 =
                                            let uu____8403 =
                                              let uu____8408 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8408, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8403 in
                                          ([], vars, uu____8402) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8391 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8420 =
                                              let uu____8423 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8423
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8420 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8442 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8442 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8450 =
                                             let uu____8451 =
                                               let uu____8458 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8458) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8451 in
                                           (uu____8450,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8469 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8469 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8480 =
                                                    let uu____8481 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8481 = cache_size in
                                                  if uu____8480
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
                                                    let uu____8497 =
                                                      let uu____8498 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8498 in
                                                    varops.mk_unique
                                                      uu____8497 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8505 =
                                                    let uu____8512 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8512) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8505 in
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
                                                      let uu____8530 =
                                                        let uu____8531 =
                                                          let uu____8538 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8538,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8531 in
                                                      [uu____8530] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8551 =
                                                    let uu____8558 =
                                                      let uu____8559 =
                                                        let uu____8570 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8570) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8559 in
                                                    (uu____8558,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8551 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8587 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8587);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8590,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8591;
                          FStar_Syntax_Syntax.lbunivs = uu____8592;
                          FStar_Syntax_Syntax.lbtyp = uu____8593;
                          FStar_Syntax_Syntax.lbeff = uu____8594;
                          FStar_Syntax_Syntax.lbdef = uu____8595;_}::uu____8596),uu____8597)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8623;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8625;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8646 ->
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
              let uu____8716 = encode_term e1 env in
              match uu____8716 with
              | (ee1,decls1) ->
                  let uu____8727 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8727 with
                   | (xs,e21) ->
                       let uu____8752 = FStar_List.hd xs in
                       (match uu____8752 with
                        | (x1,uu____8766) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8768 = encode_body e21 env' in
                            (match uu____8768 with
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
            let uu____8800 =
              let uu____8807 =
                let uu____8808 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8808 in
              gen_term_var env uu____8807 in
            match uu____8800 with
            | (scrsym,scr',env1) ->
                let uu____8816 = encode_term e env1 in
                (match uu____8816 with
                 | (scr,decls) ->
                     let uu____8827 =
                       let encode_branch b uu____8852 =
                         match uu____8852 with
                         | (else_case,decls1) ->
                             let uu____8871 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8871 with
                              | (p,w,br) ->
                                  let uu____8897 = encode_pat env1 p in
                                  (match uu____8897 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8934  ->
                                                   match uu____8934 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8941 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8963 =
                                               encode_term w1 env2 in
                                             (match uu____8963 with
                                              | (w2,decls2) ->
                                                  let uu____8976 =
                                                    let uu____8977 =
                                                      let uu____8982 =
                                                        let uu____8983 =
                                                          let uu____8988 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8988) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8983 in
                                                      (guard, uu____8982) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8977 in
                                                  (uu____8976, decls2)) in
                                       (match uu____8941 with
                                        | (guard1,decls2) ->
                                            let uu____9001 =
                                              encode_br br env2 in
                                            (match uu____9001 with
                                             | (br1,decls3) ->
                                                 let uu____9014 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9014,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8827 with
                      | (match_tm,decls1) ->
                          let uu____9033 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9033, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9073 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9073
       then
         let uu____9074 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9074
       else ());
      (let uu____9076 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9076 with
       | (vars,pat_term) ->
           let uu____9093 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9146  ->
                     fun v1  ->
                       match uu____9146 with
                       | (env1,vars1) ->
                           let uu____9198 = gen_term_var env1 v1 in
                           (match uu____9198 with
                            | (xx,uu____9220,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9093 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9299 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9300 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9301 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9309 = encode_const c env1 in
                      (match uu____9309 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9323::uu____9324 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9327 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9350 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9350 with
                        | (uu____9357,uu____9358::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9361 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9394  ->
                                  match uu____9394 with
                                  | (arg,uu____9402) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9408 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9408)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9435) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9466 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9489 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9533  ->
                                  match uu____9533 with
                                  | (arg,uu____9547) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9553 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9553)) in
                      FStar_All.pipe_right uu____9489 FStar_List.flatten in
                let pat_term1 uu____9581 = encode_term pat_term env1 in
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
      let uu____9591 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9629  ->
                fun uu____9630  ->
                  match (uu____9629, uu____9630) with
                  | ((tms,decls),(t,uu____9666)) ->
                      let uu____9687 = encode_term t env in
                      (match uu____9687 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9591 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9744 = FStar_Syntax_Util.list_elements e in
        match uu____9744 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9765 =
          let uu____9780 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9780 FStar_Syntax_Util.head_and_args in
        match uu____9765 with
        | (head1,args) ->
            let uu____9819 =
              let uu____9832 =
                let uu____9833 = FStar_Syntax_Util.un_uinst head1 in
                uu____9833.FStar_Syntax_Syntax.n in
              (uu____9832, args) in
            (match uu____9819 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9847,uu____9848)::(e,uu____9850)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9885 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9921 =
            let uu____9936 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9936 FStar_Syntax_Util.head_and_args in
          match uu____9921 with
          | (head1,args) ->
              let uu____9977 =
                let uu____9990 =
                  let uu____9991 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9991.FStar_Syntax_Syntax.n in
                (uu____9990, args) in
              (match uu____9977 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10008)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10035 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10057 = smt_pat_or1 t1 in
            (match uu____10057 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10073 = list_elements1 e in
                 FStar_All.pipe_right uu____10073
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10091 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10091
                           (FStar_List.map one_pat)))
             | uu____10102 ->
                 let uu____10107 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10107])
        | uu____10128 ->
            let uu____10131 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10131] in
      let uu____10152 =
        let uu____10171 =
          let uu____10172 = FStar_Syntax_Subst.compress t in
          uu____10172.FStar_Syntax_Syntax.n in
        match uu____10171 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10211 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10211 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10254;
                        FStar_Syntax_Syntax.effect_name = uu____10255;
                        FStar_Syntax_Syntax.result_typ = uu____10256;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10258)::(post,uu____10260)::(pats,uu____10262)::[];
                        FStar_Syntax_Syntax.flags = uu____10263;_}
                      ->
                      let uu____10304 = lemma_pats pats in
                      (binders1, pre, post, uu____10304)
                  | uu____10321 -> failwith "impos"))
        | uu____10340 -> failwith "Impos" in
      match uu____10152 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___338_10388 = env in
            {
              bindings = (uu___338_10388.bindings);
              depth = (uu___338_10388.depth);
              tcenv = (uu___338_10388.tcenv);
              warn = (uu___338_10388.warn);
              cache = (uu___338_10388.cache);
              nolabels = (uu___338_10388.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___338_10388.encode_non_total_function_typ);
              current_module_name = (uu___338_10388.current_module_name)
            } in
          let uu____10389 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10389 with
           | (vars,guards,env2,decls,uu____10414) ->
               let uu____10427 =
                 let uu____10440 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10484 =
                             let uu____10493 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10493
                               FStar_List.unzip in
                           match uu____10484 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10440 FStar_List.unzip in
               (match uu____10427 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___339_10605 = env2 in
                      {
                        bindings = (uu___339_10605.bindings);
                        depth = (uu___339_10605.depth);
                        tcenv = (uu___339_10605.tcenv);
                        warn = (uu___339_10605.warn);
                        cache = (uu___339_10605.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___339_10605.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___339_10605.encode_non_total_function_typ);
                        current_module_name =
                          (uu___339_10605.current_module_name)
                      } in
                    let uu____10606 =
                      let uu____10611 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10611 env3 in
                    (match uu____10606 with
                     | (pre1,decls'') ->
                         let uu____10618 =
                           let uu____10623 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10623 env3 in
                         (match uu____10618 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10633 =
                                let uu____10634 =
                                  let uu____10645 =
                                    let uu____10646 =
                                      let uu____10651 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10651, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10646 in
                                  (pats, vars, uu____10645) in
                                FStar_SMTEncoding_Util.mkForall uu____10634 in
                              (uu____10633, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10670 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10670
        then
          let uu____10671 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10672 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10671 uu____10672
        else () in
      let enc f r l =
        let uu____10705 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10733 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10733 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10705 with
        | (decls,args) ->
            let uu____10762 =
              let uu___340_10763 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___340_10763.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___340_10763.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10762, decls) in
      let const_op f r uu____10794 =
        let uu____10807 = f r in (uu____10807, []) in
      let un_op f l =
        let uu____10826 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10826 in
      let bin_op f uu___314_10842 =
        match uu___314_10842 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10853 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10887 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10910  ->
                 match uu____10910 with
                 | (t,uu____10924) ->
                     let uu____10925 = encode_formula t env in
                     (match uu____10925 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10887 with
        | (decls,phis) ->
            let uu____10954 =
              let uu___341_10955 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___341_10955.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___341_10955.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10954, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11016  ->
               match uu____11016 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11035) -> false
                    | uu____11036 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11051 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11051
        else
          (let uu____11065 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11065 r rf) in
      let mk_imp1 r uu___315_11090 =
        match uu___315_11090 with
        | (lhs,uu____11096)::(rhs,uu____11098)::[] ->
            let uu____11125 = encode_formula rhs env in
            (match uu____11125 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11140) ->
                      (l1, decls1)
                  | uu____11145 ->
                      let uu____11146 = encode_formula lhs env in
                      (match uu____11146 with
                       | (l2,decls2) ->
                           let uu____11157 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11157, (FStar_List.append decls1 decls2)))))
        | uu____11160 -> failwith "impossible" in
      let mk_ite r uu___316_11181 =
        match uu___316_11181 with
        | (guard,uu____11187)::(_then,uu____11189)::(_else,uu____11191)::[]
            ->
            let uu____11228 = encode_formula guard env in
            (match uu____11228 with
             | (g,decls1) ->
                 let uu____11239 = encode_formula _then env in
                 (match uu____11239 with
                  | (t,decls2) ->
                      let uu____11250 = encode_formula _else env in
                      (match uu____11250 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11264 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11289 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11289 in
      let connectives =
        let uu____11307 =
          let uu____11320 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11320) in
        let uu____11337 =
          let uu____11352 =
            let uu____11365 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11365) in
          let uu____11382 =
            let uu____11397 =
              let uu____11412 =
                let uu____11425 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11425) in
              let uu____11442 =
                let uu____11457 =
                  let uu____11472 =
                    let uu____11485 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11485) in
                  [uu____11472;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11457 in
              uu____11412 :: uu____11442 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11397 in
          uu____11352 :: uu____11382 in
        uu____11307 :: uu____11337 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11806 = encode_formula phi' env in
            (match uu____11806 with
             | (phi2,decls) ->
                 let uu____11817 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11817, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11818 ->
            let uu____11825 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11825 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11864 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11864 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11876;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11878;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11899 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11899 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11946::(x,uu____11948)::(t,uu____11950)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11997 = encode_term x env in
                 (match uu____11997 with
                  | (x1,decls) ->
                      let uu____12008 = encode_term t env in
                      (match uu____12008 with
                       | (t1,decls') ->
                           let uu____12019 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12019, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12024)::(msg,uu____12026)::(phi2,uu____12028)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12073 =
                   let uu____12078 =
                     let uu____12079 = FStar_Syntax_Subst.compress r in
                     uu____12079.FStar_Syntax_Syntax.n in
                   let uu____12082 =
                     let uu____12083 = FStar_Syntax_Subst.compress msg in
                     uu____12083.FStar_Syntax_Syntax.n in
                   (uu____12078, uu____12082) in
                 (match uu____12073 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12092))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12098 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12105)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12130 when head_redex env head2 ->
                 let uu____12143 = whnf env phi1 in
                 encode_formula uu____12143 env
             | uu____12144 ->
                 let uu____12157 = encode_term phi1 env in
                 (match uu____12157 with
                  | (tt,decls) ->
                      let uu____12168 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___342_12171 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___342_12171.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___342_12171.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12168, decls)))
        | uu____12172 ->
            let uu____12173 = encode_term phi1 env in
            (match uu____12173 with
             | (tt,decls) ->
                 let uu____12184 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___343_12187 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___343_12187.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___343_12187.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12184, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12223 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12223 with
        | (vars,guards,env2,decls,uu____12262) ->
            let uu____12275 =
              let uu____12288 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12336 =
                          let uu____12345 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12375  ->
                                    match uu____12375 with
                                    | (t,uu____12385) ->
                                        encode_term t
                                          (let uu___344_12387 = env2 in
                                           {
                                             bindings =
                                               (uu___344_12387.bindings);
                                             depth = (uu___344_12387.depth);
                                             tcenv = (uu___344_12387.tcenv);
                                             warn = (uu___344_12387.warn);
                                             cache = (uu___344_12387.cache);
                                             nolabels =
                                               (uu___344_12387.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___344_12387.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___344_12387.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12345 FStar_List.unzip in
                        match uu____12336 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12288 FStar_List.unzip in
            (match uu____12275 with
             | (pats,decls') ->
                 let uu____12486 = encode_formula body env2 in
                 (match uu____12486 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12518;
                             FStar_SMTEncoding_Term.rng = uu____12519;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12534 -> guards in
                      let uu____12539 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12539, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12599  ->
                   match uu____12599 with
                   | (x,uu____12605) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12613 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12625 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12625) uu____12613 tl1 in
             let uu____12628 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12655  ->
                       match uu____12655 with
                       | (b,uu____12661) ->
                           let uu____12662 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12662)) in
             (match uu____12628 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12668) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12682 =
                    let uu____12687 =
                      let uu____12688 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12688 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12687) in
                  FStar_Errors.log_issue pos uu____12682) in
       let uu____12689 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12689 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12698 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12756  ->
                     match uu____12756 with
                     | (l,uu____12770) -> FStar_Ident.lid_equals op l)) in
           (match uu____12698 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12803,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12843 = encode_q_body env vars pats body in
             match uu____12843 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12888 =
                     let uu____12899 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12899) in
                   FStar_SMTEncoding_Term.mkForall uu____12888
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12918 = encode_q_body env vars pats body in
             match uu____12918 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12962 =
                   let uu____12963 =
                     let uu____12974 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12974) in
                   FStar_SMTEncoding_Term.mkExists uu____12963
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12962, decls))))
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
  let uu____13067 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13067 with
  | (asym,a) ->
      let uu____13074 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13074 with
       | (xsym,x) ->
           let uu____13081 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13081 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13125 =
                      let uu____13136 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13136, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13125 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13162 =
                      let uu____13169 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13169) in
                    FStar_SMTEncoding_Util.mkApp uu____13162 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13182 =
                    let uu____13185 =
                      let uu____13188 =
                        let uu____13191 =
                          let uu____13192 =
                            let uu____13199 =
                              let uu____13200 =
                                let uu____13211 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13211) in
                              FStar_SMTEncoding_Util.mkForall uu____13200 in
                            (uu____13199, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13192 in
                        let uu____13228 =
                          let uu____13231 =
                            let uu____13232 =
                              let uu____13239 =
                                let uu____13240 =
                                  let uu____13251 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13251) in
                                FStar_SMTEncoding_Util.mkForall uu____13240 in
                              (uu____13239,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13232 in
                          [uu____13231] in
                        uu____13191 :: uu____13228 in
                      xtok_decl :: uu____13188 in
                    xname_decl :: uu____13185 in
                  (xtok1, uu____13182) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13342 =
                    let uu____13355 =
                      let uu____13364 =
                        let uu____13365 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13365 in
                      quant axy uu____13364 in
                    (FStar_Parser_Const.op_Eq, uu____13355) in
                  let uu____13374 =
                    let uu____13389 =
                      let uu____13402 =
                        let uu____13411 =
                          let uu____13412 =
                            let uu____13413 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13413 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13412 in
                        quant axy uu____13411 in
                      (FStar_Parser_Const.op_notEq, uu____13402) in
                    let uu____13422 =
                      let uu____13437 =
                        let uu____13450 =
                          let uu____13459 =
                            let uu____13460 =
                              let uu____13461 =
                                let uu____13466 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13467 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13466, uu____13467) in
                              FStar_SMTEncoding_Util.mkLT uu____13461 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13460 in
                          quant xy uu____13459 in
                        (FStar_Parser_Const.op_LT, uu____13450) in
                      let uu____13476 =
                        let uu____13491 =
                          let uu____13504 =
                            let uu____13513 =
                              let uu____13514 =
                                let uu____13515 =
                                  let uu____13520 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13521 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13520, uu____13521) in
                                FStar_SMTEncoding_Util.mkLTE uu____13515 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13514 in
                            quant xy uu____13513 in
                          (FStar_Parser_Const.op_LTE, uu____13504) in
                        let uu____13530 =
                          let uu____13545 =
                            let uu____13558 =
                              let uu____13567 =
                                let uu____13568 =
                                  let uu____13569 =
                                    let uu____13574 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13575 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13574, uu____13575) in
                                  FStar_SMTEncoding_Util.mkGT uu____13569 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13568 in
                              quant xy uu____13567 in
                            (FStar_Parser_Const.op_GT, uu____13558) in
                          let uu____13584 =
                            let uu____13599 =
                              let uu____13612 =
                                let uu____13621 =
                                  let uu____13622 =
                                    let uu____13623 =
                                      let uu____13628 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13629 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13628, uu____13629) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13623 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13622 in
                                quant xy uu____13621 in
                              (FStar_Parser_Const.op_GTE, uu____13612) in
                            let uu____13638 =
                              let uu____13653 =
                                let uu____13666 =
                                  let uu____13675 =
                                    let uu____13676 =
                                      let uu____13677 =
                                        let uu____13682 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13683 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13682, uu____13683) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13677 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13676 in
                                  quant xy uu____13675 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13666) in
                              let uu____13692 =
                                let uu____13707 =
                                  let uu____13720 =
                                    let uu____13729 =
                                      let uu____13730 =
                                        let uu____13731 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13731 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13730 in
                                    quant qx uu____13729 in
                                  (FStar_Parser_Const.op_Minus, uu____13720) in
                                let uu____13740 =
                                  let uu____13755 =
                                    let uu____13768 =
                                      let uu____13777 =
                                        let uu____13778 =
                                          let uu____13779 =
                                            let uu____13784 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13785 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13784, uu____13785) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13779 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13778 in
                                      quant xy uu____13777 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13768) in
                                  let uu____13794 =
                                    let uu____13809 =
                                      let uu____13822 =
                                        let uu____13831 =
                                          let uu____13832 =
                                            let uu____13833 =
                                              let uu____13838 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13839 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13838, uu____13839) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13833 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13832 in
                                        quant xy uu____13831 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13822) in
                                    let uu____13848 =
                                      let uu____13863 =
                                        let uu____13876 =
                                          let uu____13885 =
                                            let uu____13886 =
                                              let uu____13887 =
                                                let uu____13892 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13893 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13892, uu____13893) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13887 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13886 in
                                          quant xy uu____13885 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13876) in
                                      let uu____13902 =
                                        let uu____13917 =
                                          let uu____13930 =
                                            let uu____13939 =
                                              let uu____13940 =
                                                let uu____13941 =
                                                  let uu____13946 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13947 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13946, uu____13947) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13941 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13940 in
                                            quant xy uu____13939 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13930) in
                                        let uu____13956 =
                                          let uu____13971 =
                                            let uu____13984 =
                                              let uu____13993 =
                                                let uu____13994 =
                                                  let uu____13995 =
                                                    let uu____14000 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14001 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14000,
                                                      uu____14001) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13995 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13994 in
                                              quant xy uu____13993 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13984) in
                                          let uu____14010 =
                                            let uu____14025 =
                                              let uu____14038 =
                                                let uu____14047 =
                                                  let uu____14048 =
                                                    let uu____14049 =
                                                      let uu____14054 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14055 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14054,
                                                        uu____14055) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14049 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14048 in
                                                quant xy uu____14047 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14038) in
                                            let uu____14064 =
                                              let uu____14079 =
                                                let uu____14092 =
                                                  let uu____14101 =
                                                    let uu____14102 =
                                                      let uu____14103 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14103 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14102 in
                                                  quant qx uu____14101 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14092) in
                                              [uu____14079] in
                                            uu____14025 :: uu____14064 in
                                          uu____13971 :: uu____14010 in
                                        uu____13917 :: uu____13956 in
                                      uu____13863 :: uu____13902 in
                                    uu____13809 :: uu____13848 in
                                  uu____13755 :: uu____13794 in
                                uu____13707 :: uu____13740 in
                              uu____13653 :: uu____13692 in
                            uu____13599 :: uu____13638 in
                          uu____13545 :: uu____13584 in
                        uu____13491 :: uu____13530 in
                      uu____13437 :: uu____13476 in
                    uu____13389 :: uu____13422 in
                  uu____13342 :: uu____13374 in
                let mk1 l v1 =
                  let uu____14317 =
                    let uu____14326 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14384  ->
                              match uu____14384 with
                              | (l',uu____14398) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14326
                      (FStar_Option.map
                         (fun uu____14458  ->
                            match uu____14458 with | (uu____14477,b) -> b v1)) in
                  FStar_All.pipe_right uu____14317 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14548  ->
                          match uu____14548 with
                          | (l',uu____14562) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14600 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14600 with
        | (xxsym,xx) ->
            let uu____14607 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14607 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14617 =
                   let uu____14624 =
                     let uu____14625 =
                       let uu____14636 =
                         let uu____14637 =
                           let uu____14642 =
                             let uu____14643 =
                               let uu____14648 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14648) in
                             FStar_SMTEncoding_Util.mkEq uu____14643 in
                           (xx_has_type, uu____14642) in
                         FStar_SMTEncoding_Util.mkImp uu____14637 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14636) in
                     FStar_SMTEncoding_Util.mkForall uu____14625 in
                   let uu____14673 =
                     let uu____14674 =
                       let uu____14675 =
                         let uu____14676 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14676 in
                       Prims.strcat module_name uu____14675 in
                     varops.mk_unique uu____14674 in
                   (uu____14624, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14673) in
                 FStar_SMTEncoding_Util.mkAssume uu____14617)
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
    let uu____14712 =
      let uu____14713 =
        let uu____14720 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14720, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14713 in
    let uu____14723 =
      let uu____14726 =
        let uu____14727 =
          let uu____14734 =
            let uu____14735 =
              let uu____14746 =
                let uu____14747 =
                  let uu____14752 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14752) in
                FStar_SMTEncoding_Util.mkImp uu____14747 in
              ([[typing_pred]], [xx], uu____14746) in
            mkForall_fuel uu____14735 in
          (uu____14734, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14727 in
      [uu____14726] in
    uu____14712 :: uu____14723 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14794 =
      let uu____14795 =
        let uu____14802 =
          let uu____14803 =
            let uu____14814 =
              let uu____14819 =
                let uu____14822 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14822] in
              [uu____14819] in
            let uu____14827 =
              let uu____14828 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14828 tt in
            (uu____14814, [bb], uu____14827) in
          FStar_SMTEncoding_Util.mkForall uu____14803 in
        (uu____14802, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14795 in
    let uu____14849 =
      let uu____14852 =
        let uu____14853 =
          let uu____14860 =
            let uu____14861 =
              let uu____14872 =
                let uu____14873 =
                  let uu____14878 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14878) in
                FStar_SMTEncoding_Util.mkImp uu____14873 in
              ([[typing_pred]], [xx], uu____14872) in
            mkForall_fuel uu____14861 in
          (uu____14860, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14853 in
      [uu____14852] in
    uu____14794 :: uu____14849 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14928 =
        let uu____14929 =
          let uu____14936 =
            let uu____14939 =
              let uu____14942 =
                let uu____14945 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14946 =
                  let uu____14949 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14949] in
                uu____14945 :: uu____14946 in
              tt :: uu____14942 in
            tt :: uu____14939 in
          ("Prims.Precedes", uu____14936) in
        FStar_SMTEncoding_Util.mkApp uu____14929 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14928 in
    let precedes_y_x =
      let uu____14953 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14953 in
    let uu____14956 =
      let uu____14957 =
        let uu____14964 =
          let uu____14965 =
            let uu____14976 =
              let uu____14981 =
                let uu____14984 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14984] in
              [uu____14981] in
            let uu____14989 =
              let uu____14990 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14990 tt in
            (uu____14976, [bb], uu____14989) in
          FStar_SMTEncoding_Util.mkForall uu____14965 in
        (uu____14964, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14957 in
    let uu____15011 =
      let uu____15014 =
        let uu____15015 =
          let uu____15022 =
            let uu____15023 =
              let uu____15034 =
                let uu____15035 =
                  let uu____15040 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15040) in
                FStar_SMTEncoding_Util.mkImp uu____15035 in
              ([[typing_pred]], [xx], uu____15034) in
            mkForall_fuel uu____15023 in
          (uu____15022, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15015 in
      let uu____15065 =
        let uu____15068 =
          let uu____15069 =
            let uu____15076 =
              let uu____15077 =
                let uu____15088 =
                  let uu____15089 =
                    let uu____15094 =
                      let uu____15095 =
                        let uu____15098 =
                          let uu____15101 =
                            let uu____15104 =
                              let uu____15105 =
                                let uu____15110 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15111 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15110, uu____15111) in
                              FStar_SMTEncoding_Util.mkGT uu____15105 in
                            let uu____15112 =
                              let uu____15115 =
                                let uu____15116 =
                                  let uu____15121 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15122 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15121, uu____15122) in
                                FStar_SMTEncoding_Util.mkGTE uu____15116 in
                              let uu____15123 =
                                let uu____15126 =
                                  let uu____15127 =
                                    let uu____15132 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15133 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15132, uu____15133) in
                                  FStar_SMTEncoding_Util.mkLT uu____15127 in
                                [uu____15126] in
                              uu____15115 :: uu____15123 in
                            uu____15104 :: uu____15112 in
                          typing_pred_y :: uu____15101 in
                        typing_pred :: uu____15098 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15095 in
                    (uu____15094, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15089 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15088) in
              mkForall_fuel uu____15077 in
            (uu____15076,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15069 in
        [uu____15068] in
      uu____15014 :: uu____15065 in
    uu____14956 :: uu____15011 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15179 =
      let uu____15180 =
        let uu____15187 =
          let uu____15188 =
            let uu____15199 =
              let uu____15204 =
                let uu____15207 = FStar_SMTEncoding_Term.boxString b in
                [uu____15207] in
              [uu____15204] in
            let uu____15212 =
              let uu____15213 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15213 tt in
            (uu____15199, [bb], uu____15212) in
          FStar_SMTEncoding_Util.mkForall uu____15188 in
        (uu____15187, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15180 in
    let uu____15234 =
      let uu____15237 =
        let uu____15238 =
          let uu____15245 =
            let uu____15246 =
              let uu____15257 =
                let uu____15258 =
                  let uu____15263 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15263) in
                FStar_SMTEncoding_Util.mkImp uu____15258 in
              ([[typing_pred]], [xx], uu____15257) in
            mkForall_fuel uu____15246 in
          (uu____15245, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15238 in
      [uu____15237] in
    uu____15179 :: uu____15234 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15316 =
      let uu____15317 =
        let uu____15324 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15324, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15317 in
    [uu____15316] in
  let mk_and_interp env conj uu____15336 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15361 =
      let uu____15362 =
        let uu____15369 =
          let uu____15370 =
            let uu____15381 =
              let uu____15382 =
                let uu____15387 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15387, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15382 in
            ([[l_and_a_b]], [aa; bb], uu____15381) in
          FStar_SMTEncoding_Util.mkForall uu____15370 in
        (uu____15369, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15362 in
    [uu____15361] in
  let mk_or_interp env disj uu____15425 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15450 =
      let uu____15451 =
        let uu____15458 =
          let uu____15459 =
            let uu____15470 =
              let uu____15471 =
                let uu____15476 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15476, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15471 in
            ([[l_or_a_b]], [aa; bb], uu____15470) in
          FStar_SMTEncoding_Util.mkForall uu____15459 in
        (uu____15458, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15451 in
    [uu____15450] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15539 =
      let uu____15540 =
        let uu____15547 =
          let uu____15548 =
            let uu____15559 =
              let uu____15560 =
                let uu____15565 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15565, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15560 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15559) in
          FStar_SMTEncoding_Util.mkForall uu____15548 in
        (uu____15547, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15540 in
    [uu____15539] in
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
    let uu____15638 =
      let uu____15639 =
        let uu____15646 =
          let uu____15647 =
            let uu____15658 =
              let uu____15659 =
                let uu____15664 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15664, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15659 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15658) in
          FStar_SMTEncoding_Util.mkForall uu____15647 in
        (uu____15646, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15639 in
    [uu____15638] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15735 =
      let uu____15736 =
        let uu____15743 =
          let uu____15744 =
            let uu____15755 =
              let uu____15756 =
                let uu____15761 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15761, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15756 in
            ([[l_imp_a_b]], [aa; bb], uu____15755) in
          FStar_SMTEncoding_Util.mkForall uu____15744 in
        (uu____15743, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15736 in
    [uu____15735] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15824 =
      let uu____15825 =
        let uu____15832 =
          let uu____15833 =
            let uu____15844 =
              let uu____15845 =
                let uu____15850 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15850, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15845 in
            ([[l_iff_a_b]], [aa; bb], uu____15844) in
          FStar_SMTEncoding_Util.mkForall uu____15833 in
        (uu____15832, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15825 in
    [uu____15824] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15902 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15902 in
    let uu____15905 =
      let uu____15906 =
        let uu____15913 =
          let uu____15914 =
            let uu____15925 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15925) in
          FStar_SMTEncoding_Util.mkForall uu____15914 in
        (uu____15913, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15906 in
    [uu____15905] in
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
      let uu____15985 =
        let uu____15992 =
          let uu____15995 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15995] in
        ("Valid", uu____15992) in
      FStar_SMTEncoding_Util.mkApp uu____15985 in
    let uu____15998 =
      let uu____15999 =
        let uu____16006 =
          let uu____16007 =
            let uu____16018 =
              let uu____16019 =
                let uu____16024 =
                  let uu____16025 =
                    let uu____16036 =
                      let uu____16041 =
                        let uu____16044 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16044] in
                      [uu____16041] in
                    let uu____16049 =
                      let uu____16050 =
                        let uu____16055 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16055, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16050 in
                    (uu____16036, [xx1], uu____16049) in
                  FStar_SMTEncoding_Util.mkForall uu____16025 in
                (uu____16024, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16019 in
            ([[l_forall_a_b]], [aa; bb], uu____16018) in
          FStar_SMTEncoding_Util.mkForall uu____16007 in
        (uu____16006, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15999 in
    [uu____15998] in
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
      let uu____16137 =
        let uu____16144 =
          let uu____16147 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16147] in
        ("Valid", uu____16144) in
      FStar_SMTEncoding_Util.mkApp uu____16137 in
    let uu____16150 =
      let uu____16151 =
        let uu____16158 =
          let uu____16159 =
            let uu____16170 =
              let uu____16171 =
                let uu____16176 =
                  let uu____16177 =
                    let uu____16188 =
                      let uu____16193 =
                        let uu____16196 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16196] in
                      [uu____16193] in
                    let uu____16201 =
                      let uu____16202 =
                        let uu____16207 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16207, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16202 in
                    (uu____16188, [xx1], uu____16201) in
                  FStar_SMTEncoding_Util.mkExists uu____16177 in
                (uu____16176, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16171 in
            ([[l_exists_a_b]], [aa; bb], uu____16170) in
          FStar_SMTEncoding_Util.mkForall uu____16159 in
        (uu____16158, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16151 in
    [uu____16150] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16267 =
      let uu____16268 =
        let uu____16275 =
          let uu____16276 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16276 range_ty in
        let uu____16277 = varops.mk_unique "typing_range_const" in
        (uu____16275, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16277) in
      FStar_SMTEncoding_Util.mkAssume uu____16268 in
    [uu____16267] in
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
        let uu____16311 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16311 x1 t in
      let uu____16312 =
        let uu____16323 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16323) in
      FStar_SMTEncoding_Util.mkForall uu____16312 in
    let uu____16346 =
      let uu____16347 =
        let uu____16354 =
          let uu____16355 =
            let uu____16366 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16366) in
          FStar_SMTEncoding_Util.mkForall uu____16355 in
        (uu____16354,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16347 in
    [uu____16346] in
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
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16690 =
            FStar_Util.find_opt
              (fun uu____16716  ->
                 match uu____16716 with
                 | (l,uu____16728) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16690 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16753,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16789 = encode_function_type_as_formula t env in
        match uu____16789 with
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
              let uu____16829 =
                ((let uu____16832 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16832) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16829
              then
                let uu____16839 = new_term_constant_and_tok_from_lid env lid in
                match uu____16839 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16858 =
                        let uu____16859 = FStar_Syntax_Subst.compress t_norm in
                        uu____16859.FStar_Syntax_Syntax.n in
                      match uu____16858 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16865) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16895  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16900 -> [] in
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
                (let uu____16914 = prims.is lid in
                 if uu____16914
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16922 = prims.mk lid vname in
                   match uu____16922 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16946 =
                      let uu____16957 = curried_arrow_formals_comp t_norm in
                      match uu____16957 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16975 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16975
                            then
                              let uu____16976 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___345_16979 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___345_16979.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___345_16979.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___345_16979.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___345_16979.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___345_16979.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___345_16979.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___345_16979.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___345_16979.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___345_16979.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___345_16979.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___345_16979.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___345_16979.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___345_16979.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___345_16979.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___345_16979.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___345_16979.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___345_16979.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___345_16979.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___345_16979.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___345_16979.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___345_16979.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___345_16979.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___345_16979.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___345_16979.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___345_16979.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___345_16979.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___345_16979.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___345_16979.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___345_16979.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___345_16979.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___345_16979.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___345_16979.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___345_16979.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16976
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16991 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16991)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16946 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17036 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17036 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17057 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___317_17099  ->
                                       match uu___317_17099 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17103 =
                                             FStar_Util.prefix vars in
                                           (match uu____17103 with
                                            | (uu____17124,(xxsym,uu____17126))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17144 =
                                                  let uu____17145 =
                                                    let uu____17152 =
                                                      let uu____17153 =
                                                        let uu____17164 =
                                                          let uu____17165 =
                                                            let uu____17170 =
                                                              let uu____17171
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17171 in
                                                            (vapp,
                                                              uu____17170) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17165 in
                                                        ([[vapp]], vars,
                                                          uu____17164) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17153 in
                                                    (uu____17152,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17145 in
                                                [uu____17144])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17190 =
                                             FStar_Util.prefix vars in
                                           (match uu____17190 with
                                            | (uu____17211,(xxsym,uu____17213))
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
                                                let uu____17236 =
                                                  let uu____17237 =
                                                    let uu____17244 =
                                                      let uu____17245 =
                                                        let uu____17256 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17256) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17245 in
                                                    (uu____17244,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17237 in
                                                [uu____17236])
                                       | uu____17273 -> [])) in
                             let uu____17274 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17274 with
                              | (vars,guards,env',decls1,uu____17301) ->
                                  let uu____17314 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17323 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17323, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17325 =
                                          encode_formula p env' in
                                        (match uu____17325 with
                                         | (g,ds) ->
                                             let uu____17336 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17336,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17314 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17349 =
                                           let uu____17356 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17356) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17349 in
                                       let uu____17365 =
                                         let vname_decl =
                                           let uu____17373 =
                                             let uu____17384 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17394  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17384,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17373 in
                                         let uu____17403 =
                                           let env2 =
                                             let uu___346_17409 = env1 in
                                             {
                                               bindings =
                                                 (uu___346_17409.bindings);
                                               depth = (uu___346_17409.depth);
                                               tcenv = (uu___346_17409.tcenv);
                                               warn = (uu___346_17409.warn);
                                               cache = (uu___346_17409.cache);
                                               nolabels =
                                                 (uu___346_17409.nolabels);
                                               use_zfuel_name =
                                                 (uu___346_17409.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___346_17409.current_module_name)
                                             } in
                                           let uu____17410 =
                                             let uu____17411 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17411 in
                                           if uu____17410
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17403 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17426::uu____17427 ->
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
                                                     let uu____17467 =
                                                       let uu____17478 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17478) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17467 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17505 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17508 =
                                               match formals with
                                               | [] ->
                                                   let uu____17525 =
                                                     let uu____17526 =
                                                       let uu____17529 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17529 in
                                                     push_free_var env1 lid
                                                       vname uu____17526 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17525)
                                               | uu____17534 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17541 =
                                                       let uu____17548 =
                                                         let uu____17549 =
                                                           let uu____17560 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17560) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17549 in
                                                       (uu____17548,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17541 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17508 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17365 with
                                        | (decls2,env2) ->
                                            let uu____17603 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17611 =
                                                encode_term res_t1 env' in
                                              match uu____17611 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17624 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17624, decls) in
                                            (match uu____17603 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17635 =
                                                     let uu____17642 =
                                                       let uu____17643 =
                                                         let uu____17654 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17654) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17643 in
                                                     (uu____17642,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17635 in
                                                 let freshness =
                                                   let uu____17670 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17670
                                                   then
                                                     let uu____17675 =
                                                       let uu____17676 =
                                                         let uu____17687 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17698 =
                                                           varops.next_id () in
                                                         (vname, uu____17687,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17698) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17676 in
                                                     let uu____17701 =
                                                       let uu____17704 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17704] in
                                                     uu____17675 ::
                                                       uu____17701
                                                   else [] in
                                                 let g =
                                                   let uu____17709 =
                                                     let uu____17712 =
                                                       let uu____17715 =
                                                         let uu____17718 =
                                                           let uu____17721 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17721 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17718 in
                                                       FStar_List.append
                                                         decls3 uu____17715 in
                                                     FStar_List.append decls2
                                                       uu____17712 in
                                                   FStar_List.append decls11
                                                     uu____17709 in
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
          let uu____17752 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17752 with
          | FStar_Pervasives_Native.None  ->
              let uu____17789 = encode_free_var false env x t t_norm [] in
              (match uu____17789 with
               | (decls,env1) ->
                   let uu____17816 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17816 with
                    | (n1,x',uu____17843) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17864) ->
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
            let uu____17919 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17919 with
            | (decls,env1) ->
                let uu____17938 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17938
                then
                  let uu____17945 =
                    let uu____17948 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17948 in
                  (uu____17945, env1)
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
             (fun uu____18000  ->
                fun lb  ->
                  match uu____18000 with
                  | (decls,env1) ->
                      let uu____18020 =
                        let uu____18027 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18027
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18020 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18048 = FStar_Syntax_Util.head_and_args t in
    match uu____18048 with
    | (hd1,args) ->
        let uu____18085 =
          let uu____18086 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18086.FStar_Syntax_Syntax.n in
        (match uu____18085 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18090,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18109 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18131  ->
      fun quals  ->
        match uu____18131 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18207 = FStar_Util.first_N nbinders formals in
              match uu____18207 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18288  ->
                         fun uu____18289  ->
                           match (uu____18288, uu____18289) with
                           | ((formal,uu____18307),(binder,uu____18309)) ->
                               let uu____18318 =
                                 let uu____18325 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18325) in
                               FStar_Syntax_Syntax.NT uu____18318) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18333 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18364  ->
                              match uu____18364 with
                              | (x,i) ->
                                  let uu____18375 =
                                    let uu___347_18376 = x in
                                    let uu____18377 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___347_18376.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___347_18376.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18377
                                    } in
                                  (uu____18375, i))) in
                    FStar_All.pipe_right uu____18333
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18395 =
                      let uu____18396 = FStar_Syntax_Subst.compress body in
                      let uu____18397 =
                        let uu____18398 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18398 in
                      FStar_Syntax_Syntax.extend_app_n uu____18396
                        uu____18397 in
                    uu____18395 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18459 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18459
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___348_18462 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___348_18462.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___348_18462.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___348_18462.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___348_18462.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___348_18462.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___348_18462.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___348_18462.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___348_18462.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___348_18462.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___348_18462.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___348_18462.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___348_18462.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___348_18462.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___348_18462.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___348_18462.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___348_18462.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___348_18462.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___348_18462.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___348_18462.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___348_18462.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___348_18462.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___348_18462.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___348_18462.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___348_18462.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___348_18462.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___348_18462.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___348_18462.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___348_18462.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___348_18462.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___348_18462.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___348_18462.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___348_18462.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___348_18462.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18495 = FStar_Syntax_Util.abs_formals e in
                match uu____18495 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18559::uu____18560 ->
                         let uu____18575 =
                           let uu____18576 =
                             let uu____18579 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18579 in
                           uu____18576.FStar_Syntax_Syntax.n in
                         (match uu____18575 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18622 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18622 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18664 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18664
                                   then
                                     let uu____18699 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18699 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18793  ->
                                                   fun uu____18794  ->
                                                     match (uu____18793,
                                                             uu____18794)
                                                     with
                                                     | ((x,uu____18812),
                                                        (b,uu____18814)) ->
                                                         let uu____18823 =
                                                           let uu____18830 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18830) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18823)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18832 =
                                            let uu____18853 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18853) in
                                          (uu____18832, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18921 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18921 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19010) ->
                              let uu____19015 =
                                let uu____19036 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19036 in
                              (uu____19015, true)
                          | uu____19101 when Prims.op_Negation norm1 ->
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
                          | uu____19103 ->
                              let uu____19104 =
                                let uu____19105 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19106 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19105
                                  uu____19106 in
                              failwith uu____19104)
                     | uu____19131 ->
                         let rec aux' t_norm2 =
                           let uu____19156 =
                             let uu____19157 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19157.FStar_Syntax_Syntax.n in
                           match uu____19156 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19198 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19198 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19226 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19226 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19306)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19311 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19367 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19367
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19379 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19473  ->
                            fun lb  ->
                              match uu____19473 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19568 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19568
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19571 =
                                      let uu____19586 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19586
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19571 with
                                    | (tok,decl,env2) ->
                                        let uu____19632 =
                                          let uu____19645 =
                                            let uu____19656 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19656, tok) in
                                          uu____19645 :: toks in
                                        (uu____19632, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19379 with
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
                        | uu____19839 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19847 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19847 vars)
                            else
                              (let uu____19849 =
                                 let uu____19856 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19856) in
                               FStar_SMTEncoding_Util.mkApp uu____19849) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19938;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19940;
                             FStar_Syntax_Syntax.lbeff = uu____19941;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20004 =
                              let uu____20011 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20011 with
                              | (tcenv',uu____20029,e_t) ->
                                  let uu____20035 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20046 -> failwith "Impossible" in
                                  (match uu____20035 with
                                   | (e1,t_norm1) ->
                                       ((let uu___351_20062 = env2 in
                                         {
                                           bindings =
                                             (uu___351_20062.bindings);
                                           depth = (uu___351_20062.depth);
                                           tcenv = tcenv';
                                           warn = (uu___351_20062.warn);
                                           cache = (uu___351_20062.cache);
                                           nolabels =
                                             (uu___351_20062.nolabels);
                                           use_zfuel_name =
                                             (uu___351_20062.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___351_20062.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___351_20062.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20004 with
                             | (env',e1,t_norm1) ->
                                 let uu____20072 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20072 with
                                  | ((binders,body,uu____20093,uu____20094),curry)
                                      ->
                                      ((let uu____20105 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20105
                                        then
                                          let uu____20106 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20107 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20106 uu____20107
                                        else ());
                                       (let uu____20109 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20109 with
                                        | (vars,guards,env'1,binder_decls,uu____20136)
                                            ->
                                            let body1 =
                                              let uu____20150 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20150
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20153 =
                                              let uu____20162 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20162
                                              then
                                                let uu____20173 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20174 =
                                                  encode_formula body1 env'1 in
                                                (uu____20173, uu____20174)
                                              else
                                                (let uu____20184 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20184)) in
                                            (match uu____20153 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20207 =
                                                     let uu____20214 =
                                                       let uu____20215 =
                                                         let uu____20226 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20226) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20215 in
                                                     let uu____20237 =
                                                       let uu____20240 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20240 in
                                                     (uu____20214,
                                                       uu____20237,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20207 in
                                                 let uu____20243 =
                                                   let uu____20246 =
                                                     let uu____20249 =
                                                       let uu____20252 =
                                                         let uu____20255 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20255 in
                                                       FStar_List.append
                                                         decls2 uu____20252 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20249 in
                                                   FStar_List.append decls1
                                                     uu____20246 in
                                                 (uu____20243, env2))))))
                        | uu____20260 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20345 = varops.fresh "fuel" in
                          (uu____20345, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20348 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20436  ->
                                  fun uu____20437  ->
                                    match (uu____20436, uu____20437) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20585 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20585 in
                                        let gtok =
                                          let uu____20587 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20587 in
                                        let env4 =
                                          let uu____20589 =
                                            let uu____20592 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20592 in
                                          push_free_var env3 flid gtok
                                            uu____20589 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20348 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20748 t_norm
                              uu____20750 =
                              match (uu____20748, uu____20750) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20794;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20795;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20823 =
                                    let uu____20830 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20830 with
                                    | (tcenv',uu____20852,e_t) ->
                                        let uu____20858 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20869 ->
                                              failwith "Impossible" in
                                        (match uu____20858 with
                                         | (e1,t_norm1) ->
                                             ((let uu___352_20885 = env3 in
                                               {
                                                 bindings =
                                                   (uu___352_20885.bindings);
                                                 depth =
                                                   (uu___352_20885.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___352_20885.warn);
                                                 cache =
                                                   (uu___352_20885.cache);
                                                 nolabels =
                                                   (uu___352_20885.nolabels);
                                                 use_zfuel_name =
                                                   (uu___352_20885.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___352_20885.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___352_20885.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20823 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20900 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20900
                                         then
                                           let uu____20901 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20902 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20903 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20901 uu____20902
                                             uu____20903
                                         else ());
                                        (let uu____20905 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20905 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20942 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20942
                                               then
                                                 let uu____20943 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20944 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20945 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20946 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20943 uu____20944
                                                   uu____20945 uu____20946
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20950 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20950 with
                                               | (vars,guards,env'1,binder_decls,uu____20981)
                                                   ->
                                                   let decl_g =
                                                     let uu____20995 =
                                                       let uu____21006 =
                                                         let uu____21009 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21009 in
                                                       (g, uu____21006,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20995 in
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
                                                     let uu____21034 =
                                                       let uu____21041 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21041) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21034 in
                                                   let gsapp =
                                                     let uu____21051 =
                                                       let uu____21058 =
                                                         let uu____21061 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21061 ::
                                                           vars_tm in
                                                       (g, uu____21058) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21051 in
                                                   let gmax =
                                                     let uu____21067 =
                                                       let uu____21074 =
                                                         let uu____21077 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21077 ::
                                                           vars_tm in
                                                       (g, uu____21074) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21067 in
                                                   let body1 =
                                                     let uu____21083 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21083
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21085 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21085 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21103 =
                                                            let uu____21110 =
                                                              let uu____21111
                                                                =
                                                                let uu____21126
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
                                                                  uu____21126) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21111 in
                                                            let uu____21147 =
                                                              let uu____21150
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21150 in
                                                            (uu____21110,
                                                              uu____21147,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21103 in
                                                        let eqn_f =
                                                          let uu____21154 =
                                                            let uu____21161 =
                                                              let uu____21162
                                                                =
                                                                let uu____21173
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21173) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21162 in
                                                            (uu____21161,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21154 in
                                                        let eqn_g' =
                                                          let uu____21187 =
                                                            let uu____21194 =
                                                              let uu____21195
                                                                =
                                                                let uu____21206
                                                                  =
                                                                  let uu____21207
                                                                    =
                                                                    let uu____21212
                                                                    =
                                                                    let uu____21213
                                                                    =
                                                                    let uu____21220
                                                                    =
                                                                    let uu____21223
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21223
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21220) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21213 in
                                                                    (gsapp,
                                                                    uu____21212) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21207 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21206) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21195 in
                                                            (uu____21194,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21187 in
                                                        let uu____21246 =
                                                          let uu____21255 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21255
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21284)
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
                                                                  let uu____21309
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21309
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21314
                                                                  =
                                                                  let uu____21321
                                                                    =
                                                                    let uu____21322
                                                                    =
                                                                    let uu____21333
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21333) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21322 in
                                                                  (uu____21321,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21314 in
                                                              let uu____21354
                                                                =
                                                                let uu____21361
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21361
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21374
                                                                    =
                                                                    let uu____21377
                                                                    =
                                                                    let uu____21378
                                                                    =
                                                                    let uu____21385
                                                                    =
                                                                    let uu____21386
                                                                    =
                                                                    let uu____21397
                                                                    =
                                                                    let uu____21398
                                                                    =
                                                                    let uu____21403
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21403,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21398 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21397) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21386 in
                                                                    (uu____21385,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21378 in
                                                                    [uu____21377] in
                                                                    (d3,
                                                                    uu____21374) in
                                                              (match uu____21354
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21246
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
                            let uu____21468 =
                              let uu____21481 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21560  ->
                                   fun uu____21561  ->
                                     match (uu____21560, uu____21561) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21716 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21716 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21481 in
                            (match uu____21468 with
                             | (decls2,eqns,env01) ->
                                 let uu____21789 =
                                   let isDeclFun uu___318_21801 =
                                     match uu___318_21801 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21802 -> true
                                     | uu____21813 -> false in
                                   let uu____21814 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21814
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21789 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21854 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___319_21858  ->
                                 match uu___319_21858 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21859 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21865 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21865))) in
                      if uu____21854
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
                   let uu____21917 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21917
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
        let uu____21966 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21966 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21970 = encode_sigelt' env se in
      match uu____21970 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21986 =
                  let uu____21987 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21987 in
                [uu____21986]
            | uu____21988 ->
                let uu____21989 =
                  let uu____21992 =
                    let uu____21993 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21993 in
                  uu____21992 :: g in
                let uu____21994 =
                  let uu____21997 =
                    let uu____21998 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21998 in
                  [uu____21997] in
                FStar_List.append uu____21989 uu____21994 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22011 =
          let uu____22012 = FStar_Syntax_Subst.compress t in
          uu____22012.FStar_Syntax_Syntax.n in
        match uu____22011 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22016)) -> s = "opaque_to_smt"
        | uu____22017 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22022 =
          let uu____22023 = FStar_Syntax_Subst.compress t in
          uu____22023.FStar_Syntax_Syntax.n in
        match uu____22022 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22027)) -> s = "uninterpreted_by_smt"
        | uu____22028 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22033 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22038 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22041 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22044 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22059 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22063 =
            let uu____22064 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22064 Prims.op_Negation in
          if uu____22063
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22090 ->
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
               let uu____22110 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22110 with
               | (aname,atok,env2) ->
                   let uu____22126 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22126 with
                    | (formals,uu____22144) ->
                        let uu____22157 =
                          let uu____22162 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22162 env2 in
                        (match uu____22157 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22174 =
                                 let uu____22175 =
                                   let uu____22186 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22202  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22186,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22175 in
                               [uu____22174;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22215 =
                               let aux uu____22267 uu____22268 =
                                 match (uu____22267, uu____22268) with
                                 | ((bv,uu____22320),(env3,acc_sorts,acc)) ->
                                     let uu____22358 = gen_term_var env3 bv in
                                     (match uu____22358 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22215 with
                              | (uu____22430,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22453 =
                                      let uu____22460 =
                                        let uu____22461 =
                                          let uu____22472 =
                                            let uu____22473 =
                                              let uu____22478 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22478) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22473 in
                                          ([[app]], xs_sorts, uu____22472) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22461 in
                                      (uu____22460,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22453 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22498 =
                                      let uu____22505 =
                                        let uu____22506 =
                                          let uu____22517 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22517) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22506 in
                                      (uu____22505,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22498 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22536 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22536 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22564,uu____22565)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22566 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22566 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22583,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22589 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___320_22593  ->
                      match uu___320_22593 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22594 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22599 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22600 -> false)) in
            Prims.op_Negation uu____22589 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22609 =
               let uu____22616 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22616 env fv t quals in
             match uu____22609 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22631 =
                   let uu____22634 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22634 in
                 (uu____22631, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22642 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22642 with
           | (uu____22651,f1) ->
               let uu____22653 = encode_formula f1 env in
               (match uu____22653 with
                | (f2,decls) ->
                    let g =
                      let uu____22667 =
                        let uu____22668 =
                          let uu____22675 =
                            let uu____22678 =
                              let uu____22679 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22679 in
                            FStar_Pervasives_Native.Some uu____22678 in
                          let uu____22680 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22675, uu____22680) in
                        FStar_SMTEncoding_Util.mkAssume uu____22668 in
                      [uu____22667] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22686) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22698 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22716 =
                       let uu____22719 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22719.FStar_Syntax_Syntax.fv_name in
                     uu____22716.FStar_Syntax_Syntax.v in
                   let uu____22720 =
                     let uu____22721 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22721 in
                   if uu____22720
                   then
                     let val_decl =
                       let uu___355_22749 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___355_22749.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___355_22749.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___355_22749.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22754 = encode_sigelt' env1 val_decl in
                     match uu____22754 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22698 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22782,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22784;
                          FStar_Syntax_Syntax.lbtyp = uu____22785;
                          FStar_Syntax_Syntax.lbeff = uu____22786;
                          FStar_Syntax_Syntax.lbdef = uu____22787;_}::[]),uu____22788)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22807 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22807 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22836 =
                   let uu____22839 =
                     let uu____22840 =
                       let uu____22847 =
                         let uu____22848 =
                           let uu____22859 =
                             let uu____22860 =
                               let uu____22865 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22865) in
                             FStar_SMTEncoding_Util.mkEq uu____22860 in
                           ([[b2t_x]], [xx], uu____22859) in
                         FStar_SMTEncoding_Util.mkForall uu____22848 in
                       (uu____22847,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22840 in
                   [uu____22839] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22836 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22898,uu____22899) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___321_22908  ->
                  match uu___321_22908 with
                  | FStar_Syntax_Syntax.Discriminator uu____22909 -> true
                  | uu____22910 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22913,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22924 =
                     let uu____22925 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22925.FStar_Ident.idText in
                   uu____22924 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___322_22929  ->
                     match uu___322_22929 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22930 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22934) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___323_22951  ->
                  match uu___323_22951 with
                  | FStar_Syntax_Syntax.Projector uu____22952 -> true
                  | uu____22957 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22960 = try_lookup_free_var env l in
          (match uu____22960 with
           | FStar_Pervasives_Native.Some uu____22967 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___356_22971 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___356_22971.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___356_22971.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___356_22971.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22978) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22996) ->
          let uu____23005 = encode_sigelts env ses in
          (match uu____23005 with
           | (g,env1) ->
               let uu____23022 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___324_23045  ->
                         match uu___324_23045 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23046;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23047;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23048;_}
                             -> false
                         | uu____23051 -> true)) in
               (match uu____23022 with
                | (g',inversions) ->
                    let uu____23066 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___325_23087  ->
                              match uu___325_23087 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23088 ->
                                  true
                              | uu____23099 -> false)) in
                    (match uu____23066 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23117,tps,k,uu____23120,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___326_23137  ->
                    match uu___326_23137 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23138 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23147 = c in
              match uu____23147 with
              | (name,args,uu____23152,uu____23153,uu____23154) ->
                  let uu____23159 =
                    let uu____23160 =
                      let uu____23171 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23188  ->
                                match uu____23188 with
                                | (uu____23195,sort,uu____23197) -> sort)) in
                      (name, uu____23171, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23160 in
                  [uu____23159]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23224 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23230 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23230 FStar_Option.isNone)) in
            if uu____23224
            then []
            else
              (let uu____23262 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23262 with
               | (xxsym,xx) ->
                   let uu____23271 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23310  ->
                             fun l  ->
                               match uu____23310 with
                               | (out,decls) ->
                                   let uu____23330 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23330 with
                                    | (uu____23341,data_t) ->
                                        let uu____23343 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23343 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23389 =
                                                 let uu____23390 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23390.FStar_Syntax_Syntax.n in
                                               match uu____23389 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23401,indices) ->
                                                   indices
                                               | uu____23423 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23447  ->
                                                         match uu____23447
                                                         with
                                                         | (x,uu____23453) ->
                                                             let uu____23454
                                                               =
                                                               let uu____23455
                                                                 =
                                                                 let uu____23462
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23462,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23455 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23454)
                                                    env) in
                                             let uu____23465 =
                                               encode_args indices env1 in
                                             (match uu____23465 with
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
                                                      let uu____23491 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23507
                                                                 =
                                                                 let uu____23512
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23512,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23507)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23491
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23515 =
                                                      let uu____23516 =
                                                        let uu____23521 =
                                                          let uu____23522 =
                                                            let uu____23527 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23527,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23522 in
                                                        (out, uu____23521) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23516 in
                                                    (uu____23515,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23271 with
                    | (data_ax,decls) ->
                        let uu____23540 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23540 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23551 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23551 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23555 =
                                 let uu____23562 =
                                   let uu____23563 =
                                     let uu____23574 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23589 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23574,
                                       uu____23589) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23563 in
                                 let uu____23604 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23562,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23604) in
                               FStar_SMTEncoding_Util.mkAssume uu____23555 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23607 =
            let uu____23620 =
              let uu____23621 = FStar_Syntax_Subst.compress k in
              uu____23621.FStar_Syntax_Syntax.n in
            match uu____23620 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23666 -> (tps, k) in
          (match uu____23607 with
           | (formals,res) ->
               let uu____23689 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23689 with
                | (formals1,res1) ->
                    let uu____23700 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23700 with
                     | (vars,guards,env',binder_decls,uu____23725) ->
                         let uu____23738 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23738 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23757 =
                                  let uu____23764 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23764) in
                                FStar_SMTEncoding_Util.mkApp uu____23757 in
                              let uu____23773 =
                                let tname_decl =
                                  let uu____23783 =
                                    let uu____23784 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23816  ->
                                              match uu____23816 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23829 = varops.next_id () in
                                    (tname, uu____23784,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23829, false) in
                                  constructor_or_logic_type_decl uu____23783 in
                                let uu____23838 =
                                  match vars with
                                  | [] ->
                                      let uu____23851 =
                                        let uu____23852 =
                                          let uu____23855 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23855 in
                                        push_free_var env1 t tname
                                          uu____23852 in
                                      ([], uu____23851)
                                  | uu____23862 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23871 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23871 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23885 =
                                          let uu____23892 =
                                            let uu____23893 =
                                              let uu____23908 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23908) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23893 in
                                          (uu____23892,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23885 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23838 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23773 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23948 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23948 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23966 =
                                               let uu____23967 =
                                                 let uu____23974 =
                                                   let uu____23975 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23975 in
                                                 (uu____23974,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23967 in
                                             [uu____23966]
                                           else [] in
                                         let uu____23979 =
                                           let uu____23982 =
                                             let uu____23985 =
                                               let uu____23986 =
                                                 let uu____23993 =
                                                   let uu____23994 =
                                                     let uu____24005 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24005) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23994 in
                                                 (uu____23993,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23986 in
                                             [uu____23985] in
                                           FStar_List.append karr uu____23982 in
                                         FStar_List.append decls1 uu____23979 in
                                   let aux =
                                     let uu____24021 =
                                       let uu____24024 =
                                         inversion_axioms tapp vars in
                                       let uu____24027 =
                                         let uu____24030 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24030] in
                                       FStar_List.append uu____24024
                                         uu____24027 in
                                     FStar_List.append kindingAx uu____24021 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24037,uu____24038,uu____24039,uu____24040,uu____24041)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24049,t,uu____24051,n_tps,uu____24053) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24061 = new_term_constant_and_tok_from_lid env d in
          (match uu____24061 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24078 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24078 with
                | (formals,t_res) ->
                    let uu____24113 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24113 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24127 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24127 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24197 =
                                            mk_term_projector_name d x in
                                          (uu____24197,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24199 =
                                  let uu____24218 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24218, true) in
                                FStar_All.pipe_right uu____24199
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
                              let uu____24257 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24257 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24269::uu____24270 ->
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
                                         let uu____24315 =
                                           let uu____24326 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24326) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24315
                                     | uu____24351 -> tok_typing in
                                   let uu____24360 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24360 with
                                    | (vars',guards',env'',decls_formals,uu____24385)
                                        ->
                                        let uu____24398 =
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
                                        (match uu____24398 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24429 ->
                                                   let uu____24436 =
                                                     let uu____24437 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24437 in
                                                   [uu____24436] in
                                             let encode_elim uu____24447 =
                                               let uu____24448 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24448 with
                                               | (head1,args) ->
                                                   let uu____24491 =
                                                     let uu____24492 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24492.FStar_Syntax_Syntax.n in
                                                   (match uu____24491 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24502;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24503;_},uu____24504)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24510 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24510
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
                                                                 | uu____24553
                                                                    ->
                                                                    let uu____24554
                                                                    =
                                                                    let uu____24559
                                                                    =
                                                                    let uu____24560
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24560 in
                                                                    (FStar_Errors.Fatal_NonVaribleInductiveTypeParameter,
                                                                    uu____24559) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24554
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24576
                                                                    =
                                                                    let uu____24577
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24577 in
                                                                    if
                                                                    uu____24576
                                                                    then
                                                                    let uu____24590
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24590]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24592
                                                               =
                                                               let uu____24605
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24655
                                                                     ->
                                                                    fun
                                                                    uu____24656
                                                                     ->
                                                                    match 
                                                                    (uu____24655,
                                                                    uu____24656)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24751
                                                                    =
                                                                    let uu____24758
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24758 in
                                                                    (match uu____24751
                                                                    with
                                                                    | 
                                                                    (uu____24771,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24779
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24779
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24781
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24781
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
                                                                 uu____24605 in
                                                             (match uu____24592
                                                              with
                                                              | (uu____24796,arg_vars,elim_eqns_or_guards,uu____24799)
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
                                                                    let uu____24829
                                                                    =
                                                                    let uu____24836
                                                                    =
                                                                    let uu____24837
                                                                    =
                                                                    let uu____24848
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24859
                                                                    =
                                                                    let uu____24860
                                                                    =
                                                                    let uu____24865
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24865) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24860 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24848,
                                                                    uu____24859) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24837 in
                                                                    (uu____24836,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24829 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24888
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24888,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24890
                                                                    =
                                                                    let uu____24897
                                                                    =
                                                                    let uu____24898
                                                                    =
                                                                    let uu____24909
                                                                    =
                                                                    let uu____24914
                                                                    =
                                                                    let uu____24917
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24917] in
                                                                    [uu____24914] in
                                                                    let uu____24922
                                                                    =
                                                                    let uu____24923
                                                                    =
                                                                    let uu____24928
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24929
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24928,
                                                                    uu____24929) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24923 in
                                                                    (uu____24909,
                                                                    [x],
                                                                    uu____24922) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24898 in
                                                                    let uu____24948
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24897,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24948) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24890
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24955
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
                                                                    (let uu____24983
                                                                    =
                                                                    let uu____24984
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24984
                                                                    dapp1 in
                                                                    [uu____24983]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24955
                                                                    FStar_List.flatten in
                                                                    let uu____24991
                                                                    =
                                                                    let uu____24998
                                                                    =
                                                                    let uu____24999
                                                                    =
                                                                    let uu____25010
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25021
                                                                    =
                                                                    let uu____25022
                                                                    =
                                                                    let uu____25027
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25027) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25022 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25010,
                                                                    uu____25021) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24999 in
                                                                    (uu____24998,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24991) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25048 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25048
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
                                                                 | uu____25091
                                                                    ->
                                                                    let uu____25092
                                                                    =
                                                                    let uu____25097
                                                                    =
                                                                    let uu____25098
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25098 in
                                                                    (FStar_Errors.Fatal_NonVaribleInductiveTypeParameter,
                                                                    uu____25097) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25092
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25114
                                                                    =
                                                                    let uu____25115
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25115 in
                                                                    if
                                                                    uu____25114
                                                                    then
                                                                    let uu____25128
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25128]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25130
                                                               =
                                                               let uu____25143
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25193
                                                                     ->
                                                                    fun
                                                                    uu____25194
                                                                     ->
                                                                    match 
                                                                    (uu____25193,
                                                                    uu____25194)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25289
                                                                    =
                                                                    let uu____25296
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25296 in
                                                                    (match uu____25289
                                                                    with
                                                                    | 
                                                                    (uu____25309,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25317
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25317
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25319
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25319
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
                                                                 uu____25143 in
                                                             (match uu____25130
                                                              with
                                                              | (uu____25334,arg_vars,elim_eqns_or_guards,uu____25337)
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
                                                                    let uu____25367
                                                                    =
                                                                    let uu____25374
                                                                    =
                                                                    let uu____25375
                                                                    =
                                                                    let uu____25386
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25397
                                                                    =
                                                                    let uu____25398
                                                                    =
                                                                    let uu____25403
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25403) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25398 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25386,
                                                                    uu____25397) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25375 in
                                                                    (uu____25374,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25367 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25426
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25426,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25428
                                                                    =
                                                                    let uu____25435
                                                                    =
                                                                    let uu____25436
                                                                    =
                                                                    let uu____25447
                                                                    =
                                                                    let uu____25452
                                                                    =
                                                                    let uu____25455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25455] in
                                                                    [uu____25452] in
                                                                    let uu____25460
                                                                    =
                                                                    let uu____25461
                                                                    =
                                                                    let uu____25466
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25466,
                                                                    uu____25467) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25461 in
                                                                    (uu____25447,
                                                                    [x],
                                                                    uu____25460) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25436 in
                                                                    let uu____25486
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25435,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25486) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25428
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25493
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
                                                                    (let uu____25521
                                                                    =
                                                                    let uu____25522
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25522
                                                                    dapp1 in
                                                                    [uu____25521]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25493
                                                                    FStar_List.flatten in
                                                                    let uu____25529
                                                                    =
                                                                    let uu____25536
                                                                    =
                                                                    let uu____25537
                                                                    =
                                                                    let uu____25548
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25559
                                                                    =
                                                                    let uu____25560
                                                                    =
                                                                    let uu____25565
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25565) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25560 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25548,
                                                                    uu____25559) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25537 in
                                                                    (uu____25536,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25529) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25584 ->
                                                        ((let uu____25586 =
                                                            let uu____25591 =
                                                              let uu____25592
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25593
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25592
                                                                uu____25593 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25591) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25586);
                                                         ([], []))) in
                                             let uu____25598 = encode_elim () in
                                             (match uu____25598 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25618 =
                                                      let uu____25621 =
                                                        let uu____25624 =
                                                          let uu____25627 =
                                                            let uu____25630 =
                                                              let uu____25631
                                                                =
                                                                let uu____25642
                                                                  =
                                                                  let uu____25645
                                                                    =
                                                                    let uu____25646
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25646 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25645 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25642) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25631 in
                                                            [uu____25630] in
                                                          let uu____25651 =
                                                            let uu____25654 =
                                                              let uu____25657
                                                                =
                                                                let uu____25660
                                                                  =
                                                                  let uu____25663
                                                                    =
                                                                    let uu____25666
                                                                    =
                                                                    let uu____25669
                                                                    =
                                                                    let uu____25670
                                                                    =
                                                                    let uu____25677
                                                                    =
                                                                    let uu____25678
                                                                    =
                                                                    let uu____25689
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25689) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25678 in
                                                                    (uu____25677,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25670 in
                                                                    let uu____25702
                                                                    =
                                                                    let uu____25705
                                                                    =
                                                                    let uu____25706
                                                                    =
                                                                    let uu____25713
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    let uu____25725
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25725,
                                                                    uu____25736) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25714 in
                                                                    (uu____25713,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25706 in
                                                                    [uu____25705] in
                                                                    uu____25669
                                                                    ::
                                                                    uu____25702 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25666 in
                                                                  FStar_List.append
                                                                    uu____25663
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25660 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25657 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25654 in
                                                          FStar_List.append
                                                            uu____25627
                                                            uu____25651 in
                                                        FStar_List.append
                                                          decls3 uu____25624 in
                                                      FStar_List.append
                                                        decls2 uu____25621 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25618 in
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
           (fun uu____25782  ->
              fun se  ->
                match uu____25782 with
                | (g,env1) ->
                    let uu____25802 = encode_sigelt env1 se in
                    (match uu____25802 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25859 =
        match uu____25859 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25891 ->
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
                 ((let uu____25897 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25897
                   then
                     let uu____25898 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25899 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25900 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25898 uu____25899 uu____25900
                   else ());
                  (let uu____25902 = encode_term t1 env1 in
                   match uu____25902 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25918 =
                         let uu____25925 =
                           let uu____25926 =
                             let uu____25927 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25927
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25926 in
                         new_term_constant_from_string env1 x uu____25925 in
                       (match uu____25918 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25943 = FStar_Options.log_queries () in
                              if uu____25943
                              then
                                let uu____25946 =
                                  let uu____25947 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25948 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25949 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25947 uu____25948 uu____25949 in
                                FStar_Pervasives_Native.Some uu____25946
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25965,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25979 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25979 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26002,se,uu____26004) ->
                 let uu____26009 = encode_sigelt env1 se in
                 (match uu____26009 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26026,se) ->
                 let uu____26032 = encode_sigelt env1 se in
                 (match uu____26032 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26049 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26049 with | (uu____26072,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26084 'Auu____26085 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26085,'Auu____26084)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26153  ->
              match uu____26153 with
              | (l,uu____26165,uu____26166) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26212  ->
              match uu____26212 with
              | (l,uu____26226,uu____26227) ->
                  let uu____26236 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26237 =
                    let uu____26240 =
                      let uu____26241 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26241 in
                    [uu____26240] in
                  uu____26236 :: uu____26237)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26262 =
      let uu____26265 =
        let uu____26266 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26269 =
          let uu____26270 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26270 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26266;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26269
        } in
      [uu____26265] in
    FStar_ST.op_Colon_Equals last_env uu____26262
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26329 = FStar_ST.op_Bang last_env in
      match uu____26329 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26385 ->
          let uu___357_26388 = e in
          let uu____26389 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___357_26388.bindings);
            depth = (uu___357_26388.depth);
            tcenv;
            warn = (uu___357_26388.warn);
            cache = (uu___357_26388.cache);
            nolabels = (uu___357_26388.nolabels);
            use_zfuel_name = (uu___357_26388.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___357_26388.encode_non_total_function_typ);
            current_module_name = uu____26389
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26393 = FStar_ST.op_Bang last_env in
    match uu____26393 with
    | [] -> failwith "Empty env stack"
    | uu____26448::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26506  ->
    let uu____26507 = FStar_ST.op_Bang last_env in
    match uu____26507 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___358_26570 = hd1 in
          {
            bindings = (uu___358_26570.bindings);
            depth = (uu___358_26570.depth);
            tcenv = (uu___358_26570.tcenv);
            warn = (uu___358_26570.warn);
            cache = refs;
            nolabels = (uu___358_26570.nolabels);
            use_zfuel_name = (uu___358_26570.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___358_26570.encode_non_total_function_typ);
            current_module_name = (uu___358_26570.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26625  ->
    let uu____26626 = FStar_ST.op_Bang last_env in
    match uu____26626 with
    | [] -> failwith "Popping an empty stack"
    | uu____26681::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26774::uu____26775,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___359_26783 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___359_26783.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___359_26783.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___359_26783.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26784 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26799 =
        let uu____26802 =
          let uu____26803 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26803 in
        let uu____26804 = open_fact_db_tags env in uu____26802 :: uu____26804 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26799
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
      let uu____26826 = encode_sigelt env se in
      match uu____26826 with
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
        let uu____26862 = FStar_Options.log_queries () in
        if uu____26862
        then
          let uu____26865 =
            let uu____26866 =
              let uu____26867 =
                let uu____26868 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26868 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26867 in
            FStar_SMTEncoding_Term.Caption uu____26866 in
          uu____26865 :: decls
        else decls in
      (let uu____26879 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26879
       then
         let uu____26880 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26880
       else ());
      (let env =
         let uu____26883 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26883 tcenv in
       let uu____26884 = encode_top_level_facts env se in
       match uu____26884 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26898 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26898)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26910 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26910
       then
         let uu____26911 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26911
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26946  ->
                 fun se  ->
                   match uu____26946 with
                   | (g,env2) ->
                       let uu____26966 = encode_top_level_facts env2 se in
                       (match uu____26966 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26989 =
         encode_signature
           (let uu___360_26998 = env in
            {
              bindings = (uu___360_26998.bindings);
              depth = (uu___360_26998.depth);
              tcenv = (uu___360_26998.tcenv);
              warn = false;
              cache = (uu___360_26998.cache);
              nolabels = (uu___360_26998.nolabels);
              use_zfuel_name = (uu___360_26998.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___360_26998.encode_non_total_function_typ);
              current_module_name = (uu___360_26998.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26989 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27015 = FStar_Options.log_queries () in
             if uu____27015
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___361_27023 = env1 in
               {
                 bindings = (uu___361_27023.bindings);
                 depth = (uu___361_27023.depth);
                 tcenv = (uu___361_27023.tcenv);
                 warn = true;
                 cache = (uu___361_27023.cache);
                 nolabels = (uu___361_27023.nolabels);
                 use_zfuel_name = (uu___361_27023.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___361_27023.encode_non_total_function_typ);
                 current_module_name = (uu___361_27023.current_module_name)
               });
            (let uu____27025 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27025
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
        (let uu____27077 =
           let uu____27078 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27078.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27077);
        (let env =
           let uu____27080 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27080 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27092 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27127 = aux rest in
                 (match uu____27127 with
                  | (out,rest1) ->
                      let t =
                        let uu____27157 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27157 with
                        | FStar_Pervasives_Native.Some uu____27162 ->
                            let uu____27163 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27163
                              x.FStar_Syntax_Syntax.sort
                        | uu____27164 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27168 =
                        let uu____27171 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___362_27174 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___362_27174.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___362_27174.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27171 :: out in
                      (uu____27168, rest1))
             | uu____27179 -> ([], bindings1) in
           let uu____27186 = aux bindings in
           match uu____27186 with
           | (closing,bindings1) ->
               let uu____27211 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27211, bindings1) in
         match uu____27092 with
         | (q1,bindings1) ->
             let uu____27234 =
               let uu____27239 =
                 FStar_List.filter
                   (fun uu___327_27244  ->
                      match uu___327_27244 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27245 ->
                          false
                      | uu____27252 -> true) bindings1 in
               encode_env_bindings env uu____27239 in
             (match uu____27234 with
              | (env_decls,env1) ->
                  ((let uu____27270 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27270
                    then
                      let uu____27271 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27271
                    else ());
                   (let uu____27273 = encode_formula q1 env1 in
                    match uu____27273 with
                    | (phi,qdecls) ->
                        let uu____27294 =
                          let uu____27299 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27299 phi in
                        (match uu____27294 with
                         | (labels,phi1) ->
                             let uu____27316 = encode_labels labels in
                             (match uu____27316 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27353 =
                                      let uu____27360 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27361 =
                                        varops.mk_unique "@query" in
                                      (uu____27360,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27361) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27353 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))