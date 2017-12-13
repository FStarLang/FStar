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
      (fun uu___304_107  ->
         match uu___304_107 with
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
        let uu___327_205 = a in
        let uu____206 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____206;
          FStar_Syntax_Syntax.index =
            (uu___327_205.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___327_205.FStar_Syntax_Syntax.sort)
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
    let uu___328_1869 = x in
    let uu____1870 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1870;
      FStar_Syntax_Syntax.index = (uu___328_1869.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___328_1869.FStar_Syntax_Syntax.sort)
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
                 (fun uu___305_2317  ->
                    match uu___305_2317 with
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
           (fun uu___306_2340  ->
              match uu___306_2340 with
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
        (let uu___329_2420 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___329_2420.tcenv);
           warn = (uu___329_2420.warn);
           cache = (uu___329_2420.cache);
           nolabels = (uu___329_2420.nolabels);
           use_zfuel_name = (uu___329_2420.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___329_2420.encode_non_total_function_typ);
           current_module_name = (uu___329_2420.current_module_name)
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
        (let uu___330_2438 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___330_2438.depth);
           tcenv = (uu___330_2438.tcenv);
           warn = (uu___330_2438.warn);
           cache = (uu___330_2438.cache);
           nolabels = (uu___330_2438.nolabels);
           use_zfuel_name = (uu___330_2438.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___330_2438.encode_non_total_function_typ);
           current_module_name = (uu___330_2438.current_module_name)
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
          (let uu___331_2459 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___331_2459.depth);
             tcenv = (uu___331_2459.tcenv);
             warn = (uu___331_2459.warn);
             cache = (uu___331_2459.cache);
             nolabels = (uu___331_2459.nolabels);
             use_zfuel_name = (uu___331_2459.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___331_2459.encode_non_total_function_typ);
             current_module_name = (uu___331_2459.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___332_2469 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___332_2469.depth);
          tcenv = (uu___332_2469.tcenv);
          warn = (uu___332_2469.warn);
          cache = (uu___332_2469.cache);
          nolabels = (uu___332_2469.nolabels);
          use_zfuel_name = (uu___332_2469.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___332_2469.encode_non_total_function_typ);
          current_module_name = (uu___332_2469.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___307_2493  ->
             match uu___307_2493 with
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
        let uu___333_2564 = env in
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
          depth = (uu___333_2564.depth);
          tcenv = (uu___333_2564.tcenv);
          warn = (uu___333_2564.warn);
          cache = (uu___333_2564.cache);
          nolabels = (uu___333_2564.nolabels);
          use_zfuel_name = (uu___333_2564.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___333_2564.encode_non_total_function_typ);
          current_module_name = (uu___333_2564.current_module_name)
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
        (fun uu___308_2627  ->
           match uu___308_2627 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2666 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2683 =
        lookup_binding env
          (fun uu___309_2691  ->
             match uu___309_2691 with
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
          let uu___334_2807 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___334_2807.depth);
            tcenv = (uu___334_2807.tcenv);
            warn = (uu___334_2807.warn);
            cache = (uu___334_2807.cache);
            nolabels = (uu___334_2807.nolabels);
            use_zfuel_name = (uu___334_2807.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___334_2807.encode_non_total_function_typ);
            current_module_name = (uu___334_2807.current_module_name)
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
            let uu___335_2859 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___335_2859.depth);
              tcenv = (uu___335_2859.tcenv);
              warn = (uu___335_2859.warn);
              cache = (uu___335_2859.cache);
              nolabels = (uu___335_2859.nolabels);
              use_zfuel_name = (uu___335_2859.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___335_2859.encode_non_total_function_typ);
              current_module_name = (uu___335_2859.current_module_name)
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
        (fun uu___310_3103  ->
           match uu___310_3103 with
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
               (fun uu___311_3422  ->
                  match uu___311_3422 with
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
  fun uu___312_3520  ->
    match uu___312_3520 with
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
                           (let uu___336_6242 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___336_6242.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___336_6242.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___336_6242.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___336_6242.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___336_6242.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___336_6242.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___336_6242.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___336_6242.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___336_6242.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___336_6242.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___336_6242.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___336_6242.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___336_6242.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___336_6242.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___336_6242.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___336_6242.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___336_6242.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___336_6242.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___336_6242.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___336_6242.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___336_6242.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___336_6242.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___336_6242.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___336_6242.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___336_6242.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___336_6242.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___336_6242.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___336_6242.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___336_6242.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___336_6242.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___336_6242.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___336_6242.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___336_6242.FStar_TypeChecker_Env.dep_graph)
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
                         let uu____8263 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8263 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8262);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8265 =
                       (is_impure rc) &&
                         (let uu____8267 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8267) in
                     if uu____8265
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8274 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8274 with
                        | (vars,guards,envbody,decls,uu____8299) ->
                            let body2 =
                              let uu____8313 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8313
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8315 = encode_term body2 envbody in
                            (match uu____8315 with
                             | (body3,decls') ->
                                 let uu____8326 =
                                   let uu____8335 = codomain_eff rc in
                                   match uu____8335 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8354 = encode_term tfun env in
                                       (match uu____8354 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8326 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8386 =
                                          let uu____8397 =
                                            let uu____8398 =
                                              let uu____8403 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8403, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8398 in
                                          ([], vars, uu____8397) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8386 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8415 =
                                              let uu____8418 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8418
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8415 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8437 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8437 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8445 =
                                             let uu____8446 =
                                               let uu____8453 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8453) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8446 in
                                           (uu____8445,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8464 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8464 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8475 =
                                                    let uu____8476 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8476 = cache_size in
                                                  if uu____8475
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
                                                    let uu____8492 =
                                                      let uu____8493 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8493 in
                                                    varops.mk_unique
                                                      uu____8492 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8500 =
                                                    let uu____8507 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8507) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8500 in
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
                                                      let uu____8525 =
                                                        let uu____8526 =
                                                          let uu____8533 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8533,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8526 in
                                                      [uu____8525] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8546 =
                                                    let uu____8553 =
                                                      let uu____8554 =
                                                        let uu____8565 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8565) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8554 in
                                                    (uu____8553,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8546 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8582 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8582);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8585,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8586;
                          FStar_Syntax_Syntax.lbunivs = uu____8587;
                          FStar_Syntax_Syntax.lbtyp = uu____8588;
                          FStar_Syntax_Syntax.lbeff = uu____8589;
                          FStar_Syntax_Syntax.lbdef = uu____8590;_}::uu____8591),uu____8592)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8618;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8620;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8641 ->
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
              let uu____8711 = encode_term e1 env in
              match uu____8711 with
              | (ee1,decls1) ->
                  let uu____8722 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8722 with
                   | (xs,e21) ->
                       let uu____8747 = FStar_List.hd xs in
                       (match uu____8747 with
                        | (x1,uu____8761) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8763 = encode_body e21 env' in
                            (match uu____8763 with
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
            let uu____8795 =
              let uu____8802 =
                let uu____8803 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8803 in
              gen_term_var env uu____8802 in
            match uu____8795 with
            | (scrsym,scr',env1) ->
                let uu____8811 = encode_term e env1 in
                (match uu____8811 with
                 | (scr,decls) ->
                     let uu____8822 =
                       let encode_branch b uu____8847 =
                         match uu____8847 with
                         | (else_case,decls1) ->
                             let uu____8866 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8866 with
                              | (p,w,br) ->
                                  let uu____8892 = encode_pat env1 p in
                                  (match uu____8892 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8929  ->
                                                   match uu____8929 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8936 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8958 =
                                               encode_term w1 env2 in
                                             (match uu____8958 with
                                              | (w2,decls2) ->
                                                  let uu____8971 =
                                                    let uu____8972 =
                                                      let uu____8977 =
                                                        let uu____8978 =
                                                          let uu____8983 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8983) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8978 in
                                                      (guard, uu____8977) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8972 in
                                                  (uu____8971, decls2)) in
                                       (match uu____8936 with
                                        | (guard1,decls2) ->
                                            let uu____8996 =
                                              encode_br br env2 in
                                            (match uu____8996 with
                                             | (br1,decls3) ->
                                                 let uu____9009 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9009,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8822 with
                      | (match_tm,decls1) ->
                          let uu____9028 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9028, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9068 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9068
       then
         let uu____9069 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9069
       else ());
      (let uu____9071 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9071 with
       | (vars,pat_term) ->
           let uu____9088 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9141  ->
                     fun v1  ->
                       match uu____9141 with
                       | (env1,vars1) ->
                           let uu____9193 = gen_term_var env1 v1 in
                           (match uu____9193 with
                            | (xx,uu____9215,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9088 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9294 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9295 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9296 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9304 = encode_const c env1 in
                      (match uu____9304 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9318::uu____9319 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9322 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9345 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9345 with
                        | (uu____9352,uu____9353::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9356 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9389  ->
                                  match uu____9389 with
                                  | (arg,uu____9397) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9403 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9403)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9430) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9461 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9484 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9528  ->
                                  match uu____9528 with
                                  | (arg,uu____9542) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9548 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9548)) in
                      FStar_All.pipe_right uu____9484 FStar_List.flatten in
                let pat_term1 uu____9576 = encode_term pat_term env1 in
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
      let uu____9586 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9624  ->
                fun uu____9625  ->
                  match (uu____9624, uu____9625) with
                  | ((tms,decls),(t,uu____9661)) ->
                      let uu____9682 = encode_term t env in
                      (match uu____9682 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9586 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9739 = FStar_Syntax_Util.list_elements e in
        match uu____9739 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9760 =
          let uu____9775 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9775 FStar_Syntax_Util.head_and_args in
        match uu____9760 with
        | (head1,args) ->
            let uu____9814 =
              let uu____9827 =
                let uu____9828 = FStar_Syntax_Util.un_uinst head1 in
                uu____9828.FStar_Syntax_Syntax.n in
              (uu____9827, args) in
            (match uu____9814 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9842,uu____9843)::(e,uu____9845)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9880 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9916 =
            let uu____9931 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9931 FStar_Syntax_Util.head_and_args in
          match uu____9916 with
          | (head1,args) ->
              let uu____9972 =
                let uu____9985 =
                  let uu____9986 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9986.FStar_Syntax_Syntax.n in
                (uu____9985, args) in
              (match uu____9972 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10003)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10030 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10052 = smt_pat_or1 t1 in
            (match uu____10052 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10068 = list_elements1 e in
                 FStar_All.pipe_right uu____10068
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10086 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10086
                           (FStar_List.map one_pat)))
             | uu____10097 ->
                 let uu____10102 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10102])
        | uu____10123 ->
            let uu____10126 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10126] in
      let uu____10147 =
        let uu____10166 =
          let uu____10167 = FStar_Syntax_Subst.compress t in
          uu____10167.FStar_Syntax_Syntax.n in
        match uu____10166 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10206 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10206 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10249;
                        FStar_Syntax_Syntax.effect_name = uu____10250;
                        FStar_Syntax_Syntax.result_typ = uu____10251;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10253)::(post,uu____10255)::(pats,uu____10257)::[];
                        FStar_Syntax_Syntax.flags = uu____10258;_}
                      ->
                      let uu____10299 = lemma_pats pats in
                      (binders1, pre, post, uu____10299)
                  | uu____10316 -> failwith "impos"))
        | uu____10335 -> failwith "Impos" in
      match uu____10147 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___337_10383 = env in
            {
              bindings = (uu___337_10383.bindings);
              depth = (uu___337_10383.depth);
              tcenv = (uu___337_10383.tcenv);
              warn = (uu___337_10383.warn);
              cache = (uu___337_10383.cache);
              nolabels = (uu___337_10383.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___337_10383.encode_non_total_function_typ);
              current_module_name = (uu___337_10383.current_module_name)
            } in
          let uu____10384 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10384 with
           | (vars,guards,env2,decls,uu____10409) ->
               let uu____10422 =
                 let uu____10435 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10479 =
                             let uu____10488 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10488
                               FStar_List.unzip in
                           match uu____10479 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10435 FStar_List.unzip in
               (match uu____10422 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___338_10600 = env2 in
                      {
                        bindings = (uu___338_10600.bindings);
                        depth = (uu___338_10600.depth);
                        tcenv = (uu___338_10600.tcenv);
                        warn = (uu___338_10600.warn);
                        cache = (uu___338_10600.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___338_10600.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___338_10600.encode_non_total_function_typ);
                        current_module_name =
                          (uu___338_10600.current_module_name)
                      } in
                    let uu____10601 =
                      let uu____10606 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10606 env3 in
                    (match uu____10601 with
                     | (pre1,decls'') ->
                         let uu____10613 =
                           let uu____10618 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10618 env3 in
                         (match uu____10613 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10628 =
                                let uu____10629 =
                                  let uu____10640 =
                                    let uu____10641 =
                                      let uu____10646 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10646, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10641 in
                                  (pats, vars, uu____10640) in
                                FStar_SMTEncoding_Util.mkForall uu____10629 in
                              (uu____10628, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10665 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10665
        then
          let uu____10666 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10667 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10666 uu____10667
        else () in
      let enc f r l =
        let uu____10700 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10728 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10728 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10700 with
        | (decls,args) ->
            let uu____10757 =
              let uu___339_10758 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___339_10758.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___339_10758.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10757, decls) in
      let const_op f r uu____10789 =
        let uu____10802 = f r in (uu____10802, []) in
      let un_op f l =
        let uu____10821 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10821 in
      let bin_op f uu___313_10837 =
        match uu___313_10837 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10848 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10882 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10905  ->
                 match uu____10905 with
                 | (t,uu____10919) ->
                     let uu____10920 = encode_formula t env in
                     (match uu____10920 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10882 with
        | (decls,phis) ->
            let uu____10949 =
              let uu___340_10950 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___340_10950.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___340_10950.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10949, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11011  ->
               match uu____11011 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11030) -> false
                    | uu____11031 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11046 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11046
        else
          (let uu____11060 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11060 r rf) in
      let mk_imp1 r uu___314_11085 =
        match uu___314_11085 with
        | (lhs,uu____11091)::(rhs,uu____11093)::[] ->
            let uu____11120 = encode_formula rhs env in
            (match uu____11120 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11135) ->
                      (l1, decls1)
                  | uu____11140 ->
                      let uu____11141 = encode_formula lhs env in
                      (match uu____11141 with
                       | (l2,decls2) ->
                           let uu____11152 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11152, (FStar_List.append decls1 decls2)))))
        | uu____11155 -> failwith "impossible" in
      let mk_ite r uu___315_11176 =
        match uu___315_11176 with
        | (guard,uu____11182)::(_then,uu____11184)::(_else,uu____11186)::[]
            ->
            let uu____11223 = encode_formula guard env in
            (match uu____11223 with
             | (g,decls1) ->
                 let uu____11234 = encode_formula _then env in
                 (match uu____11234 with
                  | (t,decls2) ->
                      let uu____11245 = encode_formula _else env in
                      (match uu____11245 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11259 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11284 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11284 in
      let connectives =
        let uu____11302 =
          let uu____11315 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11315) in
        let uu____11332 =
          let uu____11347 =
            let uu____11360 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11360) in
          let uu____11377 =
            let uu____11392 =
              let uu____11407 =
                let uu____11420 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11420) in
              let uu____11437 =
                let uu____11452 =
                  let uu____11467 =
                    let uu____11480 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11480) in
                  [uu____11467;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11452 in
              uu____11407 :: uu____11437 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11392 in
          uu____11347 :: uu____11377 in
        uu____11302 :: uu____11332 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11801 = encode_formula phi' env in
            (match uu____11801 with
             | (phi2,decls) ->
                 let uu____11812 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11812, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11813 ->
            let uu____11820 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11820 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11859 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11859 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11871;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11873;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11894 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11894 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11941::(x,uu____11943)::(t,uu____11945)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11992 = encode_term x env in
                 (match uu____11992 with
                  | (x1,decls) ->
                      let uu____12003 = encode_term t env in
                      (match uu____12003 with
                       | (t1,decls') ->
                           let uu____12014 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12014, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12019)::(msg,uu____12021)::(phi2,uu____12023)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12068 =
                   let uu____12073 =
                     let uu____12074 = FStar_Syntax_Subst.compress r in
                     uu____12074.FStar_Syntax_Syntax.n in
                   let uu____12077 =
                     let uu____12078 = FStar_Syntax_Subst.compress msg in
                     uu____12078.FStar_Syntax_Syntax.n in
                   (uu____12073, uu____12077) in
                 (match uu____12068 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12087))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12093 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12100)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12125 when head_redex env head2 ->
                 let uu____12138 = whnf env phi1 in
                 encode_formula uu____12138 env
             | uu____12139 ->
                 let uu____12152 = encode_term phi1 env in
                 (match uu____12152 with
                  | (tt,decls) ->
                      let uu____12163 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___341_12166 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___341_12166.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___341_12166.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12163, decls)))
        | uu____12167 ->
            let uu____12168 = encode_term phi1 env in
            (match uu____12168 with
             | (tt,decls) ->
                 let uu____12179 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___342_12182 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___342_12182.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___342_12182.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12179, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12218 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12218 with
        | (vars,guards,env2,decls,uu____12257) ->
            let uu____12270 =
              let uu____12283 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12331 =
                          let uu____12340 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12370  ->
                                    match uu____12370 with
                                    | (t,uu____12380) ->
                                        encode_term t
                                          (let uu___343_12382 = env2 in
                                           {
                                             bindings =
                                               (uu___343_12382.bindings);
                                             depth = (uu___343_12382.depth);
                                             tcenv = (uu___343_12382.tcenv);
                                             warn = (uu___343_12382.warn);
                                             cache = (uu___343_12382.cache);
                                             nolabels =
                                               (uu___343_12382.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___343_12382.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___343_12382.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12340 FStar_List.unzip in
                        match uu____12331 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12283 FStar_List.unzip in
            (match uu____12270 with
             | (pats,decls') ->
                 let uu____12481 = encode_formula body env2 in
                 (match uu____12481 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12513;
                             FStar_SMTEncoding_Term.rng = uu____12514;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12529 -> guards in
                      let uu____12534 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12534, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12594  ->
                   match uu____12594 with
                   | (x,uu____12600) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12608 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12620 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12620) uu____12608 tl1 in
             let uu____12623 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12650  ->
                       match uu____12650 with
                       | (b,uu____12656) ->
                           let uu____12657 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12657)) in
             (match uu____12623 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12663) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12677 =
                    let uu____12678 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12678 in
                  FStar_Errors.warn pos uu____12677) in
       let uu____12679 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12679 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12688 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12746  ->
                     match uu____12746 with
                     | (l,uu____12760) -> FStar_Ident.lid_equals op l)) in
           (match uu____12688 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12793,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12833 = encode_q_body env vars pats body in
             match uu____12833 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12878 =
                     let uu____12889 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12889) in
                   FStar_SMTEncoding_Term.mkForall uu____12878
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12908 = encode_q_body env vars pats body in
             match uu____12908 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12952 =
                   let uu____12953 =
                     let uu____12964 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12964) in
                   FStar_SMTEncoding_Term.mkExists uu____12953
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12952, decls))))
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
  let uu____13057 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13057 with
  | (asym,a) ->
      let uu____13064 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13064 with
       | (xsym,x) ->
           let uu____13071 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13071 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13115 =
                      let uu____13126 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13126, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13115 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13152 =
                      let uu____13159 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13159) in
                    FStar_SMTEncoding_Util.mkApp uu____13152 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13172 =
                    let uu____13175 =
                      let uu____13178 =
                        let uu____13181 =
                          let uu____13182 =
                            let uu____13189 =
                              let uu____13190 =
                                let uu____13201 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13201) in
                              FStar_SMTEncoding_Util.mkForall uu____13190 in
                            (uu____13189, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13182 in
                        let uu____13218 =
                          let uu____13221 =
                            let uu____13222 =
                              let uu____13229 =
                                let uu____13230 =
                                  let uu____13241 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13241) in
                                FStar_SMTEncoding_Util.mkForall uu____13230 in
                              (uu____13229,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13222 in
                          [uu____13221] in
                        uu____13181 :: uu____13218 in
                      xtok_decl :: uu____13178 in
                    xname_decl :: uu____13175 in
                  (xtok1, uu____13172) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13332 =
                    let uu____13345 =
                      let uu____13354 =
                        let uu____13355 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13355 in
                      quant axy uu____13354 in
                    (FStar_Parser_Const.op_Eq, uu____13345) in
                  let uu____13364 =
                    let uu____13379 =
                      let uu____13392 =
                        let uu____13401 =
                          let uu____13402 =
                            let uu____13403 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13403 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13402 in
                        quant axy uu____13401 in
                      (FStar_Parser_Const.op_notEq, uu____13392) in
                    let uu____13412 =
                      let uu____13427 =
                        let uu____13440 =
                          let uu____13449 =
                            let uu____13450 =
                              let uu____13451 =
                                let uu____13456 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13457 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13456, uu____13457) in
                              FStar_SMTEncoding_Util.mkLT uu____13451 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13450 in
                          quant xy uu____13449 in
                        (FStar_Parser_Const.op_LT, uu____13440) in
                      let uu____13466 =
                        let uu____13481 =
                          let uu____13494 =
                            let uu____13503 =
                              let uu____13504 =
                                let uu____13505 =
                                  let uu____13510 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13511 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13510, uu____13511) in
                                FStar_SMTEncoding_Util.mkLTE uu____13505 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13504 in
                            quant xy uu____13503 in
                          (FStar_Parser_Const.op_LTE, uu____13494) in
                        let uu____13520 =
                          let uu____13535 =
                            let uu____13548 =
                              let uu____13557 =
                                let uu____13558 =
                                  let uu____13559 =
                                    let uu____13564 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13565 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13564, uu____13565) in
                                  FStar_SMTEncoding_Util.mkGT uu____13559 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13558 in
                              quant xy uu____13557 in
                            (FStar_Parser_Const.op_GT, uu____13548) in
                          let uu____13574 =
                            let uu____13589 =
                              let uu____13602 =
                                let uu____13611 =
                                  let uu____13612 =
                                    let uu____13613 =
                                      let uu____13618 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13619 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13618, uu____13619) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13613 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13612 in
                                quant xy uu____13611 in
                              (FStar_Parser_Const.op_GTE, uu____13602) in
                            let uu____13628 =
                              let uu____13643 =
                                let uu____13656 =
                                  let uu____13665 =
                                    let uu____13666 =
                                      let uu____13667 =
                                        let uu____13672 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13673 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13672, uu____13673) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13667 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13666 in
                                  quant xy uu____13665 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13656) in
                              let uu____13682 =
                                let uu____13697 =
                                  let uu____13710 =
                                    let uu____13719 =
                                      let uu____13720 =
                                        let uu____13721 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13721 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13720 in
                                    quant qx uu____13719 in
                                  (FStar_Parser_Const.op_Minus, uu____13710) in
                                let uu____13730 =
                                  let uu____13745 =
                                    let uu____13758 =
                                      let uu____13767 =
                                        let uu____13768 =
                                          let uu____13769 =
                                            let uu____13774 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13775 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13774, uu____13775) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13769 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13768 in
                                      quant xy uu____13767 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13758) in
                                  let uu____13784 =
                                    let uu____13799 =
                                      let uu____13812 =
                                        let uu____13821 =
                                          let uu____13822 =
                                            let uu____13823 =
                                              let uu____13828 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13829 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13828, uu____13829) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13823 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13822 in
                                        quant xy uu____13821 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13812) in
                                    let uu____13838 =
                                      let uu____13853 =
                                        let uu____13866 =
                                          let uu____13875 =
                                            let uu____13876 =
                                              let uu____13877 =
                                                let uu____13882 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13883 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13882, uu____13883) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13877 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13876 in
                                          quant xy uu____13875 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13866) in
                                      let uu____13892 =
                                        let uu____13907 =
                                          let uu____13920 =
                                            let uu____13929 =
                                              let uu____13930 =
                                                let uu____13931 =
                                                  let uu____13936 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13937 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13936, uu____13937) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13931 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13930 in
                                            quant xy uu____13929 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13920) in
                                        let uu____13946 =
                                          let uu____13961 =
                                            let uu____13974 =
                                              let uu____13983 =
                                                let uu____13984 =
                                                  let uu____13985 =
                                                    let uu____13990 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13991 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13990,
                                                      uu____13991) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13985 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13984 in
                                              quant xy uu____13983 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13974) in
                                          let uu____14000 =
                                            let uu____14015 =
                                              let uu____14028 =
                                                let uu____14037 =
                                                  let uu____14038 =
                                                    let uu____14039 =
                                                      let uu____14044 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14045 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14044,
                                                        uu____14045) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14039 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14038 in
                                                quant xy uu____14037 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14028) in
                                            let uu____14054 =
                                              let uu____14069 =
                                                let uu____14082 =
                                                  let uu____14091 =
                                                    let uu____14092 =
                                                      let uu____14093 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14093 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14092 in
                                                  quant qx uu____14091 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14082) in
                                              [uu____14069] in
                                            uu____14015 :: uu____14054 in
                                          uu____13961 :: uu____14000 in
                                        uu____13907 :: uu____13946 in
                                      uu____13853 :: uu____13892 in
                                    uu____13799 :: uu____13838 in
                                  uu____13745 :: uu____13784 in
                                uu____13697 :: uu____13730 in
                              uu____13643 :: uu____13682 in
                            uu____13589 :: uu____13628 in
                          uu____13535 :: uu____13574 in
                        uu____13481 :: uu____13520 in
                      uu____13427 :: uu____13466 in
                    uu____13379 :: uu____13412 in
                  uu____13332 :: uu____13364 in
                let mk1 l v1 =
                  let uu____14307 =
                    let uu____14316 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14374  ->
                              match uu____14374 with
                              | (l',uu____14388) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14316
                      (FStar_Option.map
                         (fun uu____14448  ->
                            match uu____14448 with | (uu____14467,b) -> b v1)) in
                  FStar_All.pipe_right uu____14307 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14538  ->
                          match uu____14538 with
                          | (l',uu____14552) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14590 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14590 with
        | (xxsym,xx) ->
            let uu____14597 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14597 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14607 =
                   let uu____14614 =
                     let uu____14615 =
                       let uu____14626 =
                         let uu____14627 =
                           let uu____14632 =
                             let uu____14633 =
                               let uu____14638 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14638) in
                             FStar_SMTEncoding_Util.mkEq uu____14633 in
                           (xx_has_type, uu____14632) in
                         FStar_SMTEncoding_Util.mkImp uu____14627 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14626) in
                     FStar_SMTEncoding_Util.mkForall uu____14615 in
                   let uu____14663 =
                     let uu____14664 =
                       let uu____14665 =
                         let uu____14666 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14666 in
                       Prims.strcat module_name uu____14665 in
                     varops.mk_unique uu____14664 in
                   (uu____14614, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14663) in
                 FStar_SMTEncoding_Util.mkAssume uu____14607)
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
    let uu____14702 =
      let uu____14703 =
        let uu____14710 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14710, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14703 in
    let uu____14713 =
      let uu____14716 =
        let uu____14717 =
          let uu____14724 =
            let uu____14725 =
              let uu____14736 =
                let uu____14737 =
                  let uu____14742 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14742) in
                FStar_SMTEncoding_Util.mkImp uu____14737 in
              ([[typing_pred]], [xx], uu____14736) in
            mkForall_fuel uu____14725 in
          (uu____14724, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14717 in
      [uu____14716] in
    uu____14702 :: uu____14713 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14784 =
      let uu____14785 =
        let uu____14792 =
          let uu____14793 =
            let uu____14804 =
              let uu____14809 =
                let uu____14812 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14812] in
              [uu____14809] in
            let uu____14817 =
              let uu____14818 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14818 tt in
            (uu____14804, [bb], uu____14817) in
          FStar_SMTEncoding_Util.mkForall uu____14793 in
        (uu____14792, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14785 in
    let uu____14839 =
      let uu____14842 =
        let uu____14843 =
          let uu____14850 =
            let uu____14851 =
              let uu____14862 =
                let uu____14863 =
                  let uu____14868 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14868) in
                FStar_SMTEncoding_Util.mkImp uu____14863 in
              ([[typing_pred]], [xx], uu____14862) in
            mkForall_fuel uu____14851 in
          (uu____14850, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14843 in
      [uu____14842] in
    uu____14784 :: uu____14839 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14918 =
        let uu____14919 =
          let uu____14926 =
            let uu____14929 =
              let uu____14932 =
                let uu____14935 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14936 =
                  let uu____14939 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14939] in
                uu____14935 :: uu____14936 in
              tt :: uu____14932 in
            tt :: uu____14929 in
          ("Prims.Precedes", uu____14926) in
        FStar_SMTEncoding_Util.mkApp uu____14919 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14918 in
    let precedes_y_x =
      let uu____14943 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14943 in
    let uu____14946 =
      let uu____14947 =
        let uu____14954 =
          let uu____14955 =
            let uu____14966 =
              let uu____14971 =
                let uu____14974 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14974] in
              [uu____14971] in
            let uu____14979 =
              let uu____14980 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14980 tt in
            (uu____14966, [bb], uu____14979) in
          FStar_SMTEncoding_Util.mkForall uu____14955 in
        (uu____14954, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14947 in
    let uu____15001 =
      let uu____15004 =
        let uu____15005 =
          let uu____15012 =
            let uu____15013 =
              let uu____15024 =
                let uu____15025 =
                  let uu____15030 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15030) in
                FStar_SMTEncoding_Util.mkImp uu____15025 in
              ([[typing_pred]], [xx], uu____15024) in
            mkForall_fuel uu____15013 in
          (uu____15012, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15005 in
      let uu____15055 =
        let uu____15058 =
          let uu____15059 =
            let uu____15066 =
              let uu____15067 =
                let uu____15078 =
                  let uu____15079 =
                    let uu____15084 =
                      let uu____15085 =
                        let uu____15088 =
                          let uu____15091 =
                            let uu____15094 =
                              let uu____15095 =
                                let uu____15100 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15101 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15100, uu____15101) in
                              FStar_SMTEncoding_Util.mkGT uu____15095 in
                            let uu____15102 =
                              let uu____15105 =
                                let uu____15106 =
                                  let uu____15111 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15112 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15111, uu____15112) in
                                FStar_SMTEncoding_Util.mkGTE uu____15106 in
                              let uu____15113 =
                                let uu____15116 =
                                  let uu____15117 =
                                    let uu____15122 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15123 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15122, uu____15123) in
                                  FStar_SMTEncoding_Util.mkLT uu____15117 in
                                [uu____15116] in
                              uu____15105 :: uu____15113 in
                            uu____15094 :: uu____15102 in
                          typing_pred_y :: uu____15091 in
                        typing_pred :: uu____15088 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15085 in
                    (uu____15084, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15079 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15078) in
              mkForall_fuel uu____15067 in
            (uu____15066,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15059 in
        [uu____15058] in
      uu____15004 :: uu____15055 in
    uu____14946 :: uu____15001 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15169 =
      let uu____15170 =
        let uu____15177 =
          let uu____15178 =
            let uu____15189 =
              let uu____15194 =
                let uu____15197 = FStar_SMTEncoding_Term.boxString b in
                [uu____15197] in
              [uu____15194] in
            let uu____15202 =
              let uu____15203 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15203 tt in
            (uu____15189, [bb], uu____15202) in
          FStar_SMTEncoding_Util.mkForall uu____15178 in
        (uu____15177, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15170 in
    let uu____15224 =
      let uu____15227 =
        let uu____15228 =
          let uu____15235 =
            let uu____15236 =
              let uu____15247 =
                let uu____15248 =
                  let uu____15253 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15253) in
                FStar_SMTEncoding_Util.mkImp uu____15248 in
              ([[typing_pred]], [xx], uu____15247) in
            mkForall_fuel uu____15236 in
          (uu____15235, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15228 in
      [uu____15227] in
    uu____15169 :: uu____15224 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15306 =
      let uu____15307 =
        let uu____15314 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15314, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15307 in
    [uu____15306] in
  let mk_and_interp env conj uu____15326 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15351 =
      let uu____15352 =
        let uu____15359 =
          let uu____15360 =
            let uu____15371 =
              let uu____15372 =
                let uu____15377 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15377, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15372 in
            ([[l_and_a_b]], [aa; bb], uu____15371) in
          FStar_SMTEncoding_Util.mkForall uu____15360 in
        (uu____15359, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15352 in
    [uu____15351] in
  let mk_or_interp env disj uu____15415 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15440 =
      let uu____15441 =
        let uu____15448 =
          let uu____15449 =
            let uu____15460 =
              let uu____15461 =
                let uu____15466 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15466, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15461 in
            ([[l_or_a_b]], [aa; bb], uu____15460) in
          FStar_SMTEncoding_Util.mkForall uu____15449 in
        (uu____15448, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15441 in
    [uu____15440] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15529 =
      let uu____15530 =
        let uu____15537 =
          let uu____15538 =
            let uu____15549 =
              let uu____15550 =
                let uu____15555 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15555, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15550 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15549) in
          FStar_SMTEncoding_Util.mkForall uu____15538 in
        (uu____15537, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15530 in
    [uu____15529] in
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
    let uu____15628 =
      let uu____15629 =
        let uu____15636 =
          let uu____15637 =
            let uu____15648 =
              let uu____15649 =
                let uu____15654 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15654, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15649 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15648) in
          FStar_SMTEncoding_Util.mkForall uu____15637 in
        (uu____15636, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15629 in
    [uu____15628] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15725 =
      let uu____15726 =
        let uu____15733 =
          let uu____15734 =
            let uu____15745 =
              let uu____15746 =
                let uu____15751 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15751, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15746 in
            ([[l_imp_a_b]], [aa; bb], uu____15745) in
          FStar_SMTEncoding_Util.mkForall uu____15734 in
        (uu____15733, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15726 in
    [uu____15725] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15814 =
      let uu____15815 =
        let uu____15822 =
          let uu____15823 =
            let uu____15834 =
              let uu____15835 =
                let uu____15840 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15840, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15835 in
            ([[l_iff_a_b]], [aa; bb], uu____15834) in
          FStar_SMTEncoding_Util.mkForall uu____15823 in
        (uu____15822, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15815 in
    [uu____15814] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15892 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15892 in
    let uu____15895 =
      let uu____15896 =
        let uu____15903 =
          let uu____15904 =
            let uu____15915 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15915) in
          FStar_SMTEncoding_Util.mkForall uu____15904 in
        (uu____15903, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15896 in
    [uu____15895] in
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
      let uu____15975 =
        let uu____15982 =
          let uu____15985 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15985] in
        ("Valid", uu____15982) in
      FStar_SMTEncoding_Util.mkApp uu____15975 in
    let uu____15988 =
      let uu____15989 =
        let uu____15996 =
          let uu____15997 =
            let uu____16008 =
              let uu____16009 =
                let uu____16014 =
                  let uu____16015 =
                    let uu____16026 =
                      let uu____16031 =
                        let uu____16034 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16034] in
                      [uu____16031] in
                    let uu____16039 =
                      let uu____16040 =
                        let uu____16045 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16045, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16040 in
                    (uu____16026, [xx1], uu____16039) in
                  FStar_SMTEncoding_Util.mkForall uu____16015 in
                (uu____16014, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16009 in
            ([[l_forall_a_b]], [aa; bb], uu____16008) in
          FStar_SMTEncoding_Util.mkForall uu____15997 in
        (uu____15996, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15989 in
    [uu____15988] in
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
      let uu____16127 =
        let uu____16134 =
          let uu____16137 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16137] in
        ("Valid", uu____16134) in
      FStar_SMTEncoding_Util.mkApp uu____16127 in
    let uu____16140 =
      let uu____16141 =
        let uu____16148 =
          let uu____16149 =
            let uu____16160 =
              let uu____16161 =
                let uu____16166 =
                  let uu____16167 =
                    let uu____16178 =
                      let uu____16183 =
                        let uu____16186 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16186] in
                      [uu____16183] in
                    let uu____16191 =
                      let uu____16192 =
                        let uu____16197 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16197, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16192 in
                    (uu____16178, [xx1], uu____16191) in
                  FStar_SMTEncoding_Util.mkExists uu____16167 in
                (uu____16166, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16161 in
            ([[l_exists_a_b]], [aa; bb], uu____16160) in
          FStar_SMTEncoding_Util.mkForall uu____16149 in
        (uu____16148, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16141 in
    [uu____16140] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16257 =
      let uu____16258 =
        let uu____16265 =
          let uu____16266 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16266 range_ty in
        let uu____16267 = varops.mk_unique "typing_range_const" in
        (uu____16265, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16267) in
      FStar_SMTEncoding_Util.mkAssume uu____16258 in
    [uu____16257] in
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
        let uu____16301 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16301 x1 t in
      let uu____16302 =
        let uu____16313 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16313) in
      FStar_SMTEncoding_Util.mkForall uu____16302 in
    let uu____16336 =
      let uu____16337 =
        let uu____16344 =
          let uu____16345 =
            let uu____16356 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16356) in
          FStar_SMTEncoding_Util.mkForall uu____16345 in
        (uu____16344,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16337 in
    [uu____16336] in
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
          let uu____16680 =
            FStar_Util.find_opt
              (fun uu____16706  ->
                 match uu____16706 with
                 | (l,uu____16718) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16680 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16743,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16779 = encode_function_type_as_formula t env in
        match uu____16779 with
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
              let uu____16819 =
                ((let uu____16822 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16822) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16819
              then
                let uu____16829 = new_term_constant_and_tok_from_lid env lid in
                match uu____16829 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16848 =
                        let uu____16849 = FStar_Syntax_Subst.compress t_norm in
                        uu____16849.FStar_Syntax_Syntax.n in
                      match uu____16848 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16855) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16885  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16890 -> [] in
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
                (let uu____16904 = prims.is lid in
                 if uu____16904
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16912 = prims.mk lid vname in
                   match uu____16912 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16936 =
                      let uu____16947 = curried_arrow_formals_comp t_norm in
                      match uu____16947 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16965 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16965
                            then
                              let uu____16966 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___344_16969 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___344_16969.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___344_16969.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___344_16969.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___344_16969.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___344_16969.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___344_16969.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___344_16969.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___344_16969.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___344_16969.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___344_16969.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___344_16969.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___344_16969.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___344_16969.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___344_16969.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___344_16969.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___344_16969.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___344_16969.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___344_16969.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___344_16969.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___344_16969.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___344_16969.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___344_16969.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___344_16969.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___344_16969.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___344_16969.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___344_16969.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___344_16969.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___344_16969.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___344_16969.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___344_16969.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___344_16969.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___344_16969.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___344_16969.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16966
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16981 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16981)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16936 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17026 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17026 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17047 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___316_17089  ->
                                       match uu___316_17089 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17093 =
                                             FStar_Util.prefix vars in
                                           (match uu____17093 with
                                            | (uu____17114,(xxsym,uu____17116))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17134 =
                                                  let uu____17135 =
                                                    let uu____17142 =
                                                      let uu____17143 =
                                                        let uu____17154 =
                                                          let uu____17155 =
                                                            let uu____17160 =
                                                              let uu____17161
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17161 in
                                                            (vapp,
                                                              uu____17160) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17155 in
                                                        ([[vapp]], vars,
                                                          uu____17154) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17143 in
                                                    (uu____17142,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17135 in
                                                [uu____17134])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17180 =
                                             FStar_Util.prefix vars in
                                           (match uu____17180 with
                                            | (uu____17201,(xxsym,uu____17203))
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
                                                let uu____17226 =
                                                  let uu____17227 =
                                                    let uu____17234 =
                                                      let uu____17235 =
                                                        let uu____17246 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17246) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17235 in
                                                    (uu____17234,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17227 in
                                                [uu____17226])
                                       | uu____17263 -> [])) in
                             let uu____17264 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17264 with
                              | (vars,guards,env',decls1,uu____17291) ->
                                  let uu____17304 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17313 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17313, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17315 =
                                          encode_formula p env' in
                                        (match uu____17315 with
                                         | (g,ds) ->
                                             let uu____17326 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17326,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17304 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17339 =
                                           let uu____17346 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17346) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17339 in
                                       let uu____17355 =
                                         let vname_decl =
                                           let uu____17363 =
                                             let uu____17374 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17384  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17374,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17363 in
                                         let uu____17393 =
                                           let env2 =
                                             let uu___345_17399 = env1 in
                                             {
                                               bindings =
                                                 (uu___345_17399.bindings);
                                               depth = (uu___345_17399.depth);
                                               tcenv = (uu___345_17399.tcenv);
                                               warn = (uu___345_17399.warn);
                                               cache = (uu___345_17399.cache);
                                               nolabels =
                                                 (uu___345_17399.nolabels);
                                               use_zfuel_name =
                                                 (uu___345_17399.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___345_17399.current_module_name)
                                             } in
                                           let uu____17400 =
                                             let uu____17401 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17401 in
                                           if uu____17400
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17393 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17416::uu____17417 ->
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
                                                     let uu____17457 =
                                                       let uu____17468 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17468) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17457 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17495 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17498 =
                                               match formals with
                                               | [] ->
                                                   let uu____17515 =
                                                     let uu____17516 =
                                                       let uu____17519 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17519 in
                                                     push_free_var env1 lid
                                                       vname uu____17516 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17515)
                                               | uu____17524 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17531 =
                                                       let uu____17538 =
                                                         let uu____17539 =
                                                           let uu____17550 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17550) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17539 in
                                                       (uu____17538,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17531 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17498 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17355 with
                                        | (decls2,env2) ->
                                            let uu____17593 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17601 =
                                                encode_term res_t1 env' in
                                              match uu____17601 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17614 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17614, decls) in
                                            (match uu____17593 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17625 =
                                                     let uu____17632 =
                                                       let uu____17633 =
                                                         let uu____17644 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17644) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17633 in
                                                     (uu____17632,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17625 in
                                                 let freshness =
                                                   let uu____17660 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17660
                                                   then
                                                     let uu____17665 =
                                                       let uu____17666 =
                                                         let uu____17677 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17688 =
                                                           varops.next_id () in
                                                         (vname, uu____17677,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17688) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17666 in
                                                     let uu____17691 =
                                                       let uu____17694 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17694] in
                                                     uu____17665 ::
                                                       uu____17691
                                                   else [] in
                                                 let g =
                                                   let uu____17699 =
                                                     let uu____17702 =
                                                       let uu____17705 =
                                                         let uu____17708 =
                                                           let uu____17711 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17711 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17708 in
                                                       FStar_List.append
                                                         decls3 uu____17705 in
                                                     FStar_List.append decls2
                                                       uu____17702 in
                                                   FStar_List.append decls11
                                                     uu____17699 in
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
          let uu____17742 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17742 with
          | FStar_Pervasives_Native.None  ->
              let uu____17779 = encode_free_var false env x t t_norm [] in
              (match uu____17779 with
               | (decls,env1) ->
                   let uu____17806 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17806 with
                    | (n1,x',uu____17833) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17854) ->
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
            let uu____17909 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17909 with
            | (decls,env1) ->
                let uu____17928 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17928
                then
                  let uu____17935 =
                    let uu____17938 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17938 in
                  (uu____17935, env1)
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
             (fun uu____17990  ->
                fun lb  ->
                  match uu____17990 with
                  | (decls,env1) ->
                      let uu____18010 =
                        let uu____18017 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18017
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18010 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18038 = FStar_Syntax_Util.head_and_args t in
    match uu____18038 with
    | (hd1,args) ->
        let uu____18075 =
          let uu____18076 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18076.FStar_Syntax_Syntax.n in
        (match uu____18075 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18080,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18099 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18121  ->
      fun quals  ->
        match uu____18121 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18197 = FStar_Util.first_N nbinders formals in
              match uu____18197 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18278  ->
                         fun uu____18279  ->
                           match (uu____18278, uu____18279) with
                           | ((formal,uu____18297),(binder,uu____18299)) ->
                               let uu____18308 =
                                 let uu____18315 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18315) in
                               FStar_Syntax_Syntax.NT uu____18308) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18323 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18354  ->
                              match uu____18354 with
                              | (x,i) ->
                                  let uu____18365 =
                                    let uu___346_18366 = x in
                                    let uu____18367 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___346_18366.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___346_18366.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18367
                                    } in
                                  (uu____18365, i))) in
                    FStar_All.pipe_right uu____18323
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18385 =
                      let uu____18386 = FStar_Syntax_Subst.compress body in
                      let uu____18387 =
                        let uu____18388 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18388 in
                      FStar_Syntax_Syntax.extend_app_n uu____18386
                        uu____18387 in
                    uu____18385 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18449 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18449
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___347_18452 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___347_18452.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___347_18452.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___347_18452.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___347_18452.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___347_18452.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___347_18452.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___347_18452.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___347_18452.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___347_18452.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___347_18452.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___347_18452.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___347_18452.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___347_18452.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___347_18452.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___347_18452.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___347_18452.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___347_18452.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___347_18452.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___347_18452.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___347_18452.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___347_18452.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___347_18452.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___347_18452.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___347_18452.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___347_18452.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___347_18452.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___347_18452.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___347_18452.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___347_18452.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___347_18452.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___347_18452.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___347_18452.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___347_18452.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18485 = FStar_Syntax_Util.abs_formals e in
                match uu____18485 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18549::uu____18550 ->
                         let uu____18565 =
                           let uu____18566 =
                             let uu____18569 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18569 in
                           uu____18566.FStar_Syntax_Syntax.n in
                         (match uu____18565 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18612 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18612 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18654 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18654
                                   then
                                     let uu____18689 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18689 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18783  ->
                                                   fun uu____18784  ->
                                                     match (uu____18783,
                                                             uu____18784)
                                                     with
                                                     | ((x,uu____18802),
                                                        (b,uu____18804)) ->
                                                         let uu____18813 =
                                                           let uu____18820 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18820) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18813)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18822 =
                                            let uu____18843 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18843) in
                                          (uu____18822, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18911 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18911 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19000) ->
                              let uu____19005 =
                                let uu____19026 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19026 in
                              (uu____19005, true)
                          | uu____19091 when Prims.op_Negation norm1 ->
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
                          | uu____19093 ->
                              let uu____19094 =
                                let uu____19095 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19096 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19095
                                  uu____19096 in
                              failwith uu____19094)
                     | uu____19121 ->
                         let rec aux' t_norm2 =
                           let uu____19146 =
                             let uu____19147 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19147.FStar_Syntax_Syntax.n in
                           match uu____19146 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19188 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19188 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19216 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19216 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19296)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19301 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19357 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19357
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19369 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19463  ->
                            fun lb  ->
                              match uu____19463 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19558 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19558
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19561 =
                                      let uu____19576 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19576
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19561 with
                                    | (tok,decl,env2) ->
                                        let uu____19622 =
                                          let uu____19635 =
                                            let uu____19646 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19646, tok) in
                                          uu____19635 :: toks in
                                        (uu____19622, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19369 with
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
                        | uu____19829 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19837 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19837 vars)
                            else
                              (let uu____19839 =
                                 let uu____19846 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19846) in
                               FStar_SMTEncoding_Util.mkApp uu____19839) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19928;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19930;
                             FStar_Syntax_Syntax.lbeff = uu____19931;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19994 =
                              let uu____20001 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20001 with
                              | (tcenv',uu____20019,e_t) ->
                                  let uu____20025 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20036 -> failwith "Impossible" in
                                  (match uu____20025 with
                                   | (e1,t_norm1) ->
                                       ((let uu___350_20052 = env2 in
                                         {
                                           bindings =
                                             (uu___350_20052.bindings);
                                           depth = (uu___350_20052.depth);
                                           tcenv = tcenv';
                                           warn = (uu___350_20052.warn);
                                           cache = (uu___350_20052.cache);
                                           nolabels =
                                             (uu___350_20052.nolabels);
                                           use_zfuel_name =
                                             (uu___350_20052.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___350_20052.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___350_20052.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19994 with
                             | (env',e1,t_norm1) ->
                                 let uu____20062 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20062 with
                                  | ((binders,body,uu____20083,uu____20084),curry)
                                      ->
                                      ((let uu____20095 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20095
                                        then
                                          let uu____20096 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20097 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20096 uu____20097
                                        else ());
                                       (let uu____20099 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20099 with
                                        | (vars,guards,env'1,binder_decls,uu____20126)
                                            ->
                                            let body1 =
                                              let uu____20140 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20140
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20143 =
                                              let uu____20152 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20152
                                              then
                                                let uu____20163 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20164 =
                                                  encode_formula body1 env'1 in
                                                (uu____20163, uu____20164)
                                              else
                                                (let uu____20174 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20174)) in
                                            (match uu____20143 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20197 =
                                                     let uu____20204 =
                                                       let uu____20205 =
                                                         let uu____20216 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20216) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20205 in
                                                     let uu____20227 =
                                                       let uu____20230 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20230 in
                                                     (uu____20204,
                                                       uu____20227,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20197 in
                                                 let uu____20233 =
                                                   let uu____20236 =
                                                     let uu____20239 =
                                                       let uu____20242 =
                                                         let uu____20245 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20245 in
                                                       FStar_List.append
                                                         decls2 uu____20242 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20239 in
                                                   FStar_List.append decls1
                                                     uu____20236 in
                                                 (uu____20233, env2))))))
                        | uu____20250 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20335 = varops.fresh "fuel" in
                          (uu____20335, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20338 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20426  ->
                                  fun uu____20427  ->
                                    match (uu____20426, uu____20427) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20575 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20575 in
                                        let gtok =
                                          let uu____20577 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20577 in
                                        let env4 =
                                          let uu____20579 =
                                            let uu____20582 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20582 in
                                          push_free_var env3 flid gtok
                                            uu____20579 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20338 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20738 t_norm
                              uu____20740 =
                              match (uu____20738, uu____20740) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20784;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20785;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20813 =
                                    let uu____20820 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20820 with
                                    | (tcenv',uu____20842,e_t) ->
                                        let uu____20848 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20859 ->
                                              failwith "Impossible" in
                                        (match uu____20848 with
                                         | (e1,t_norm1) ->
                                             ((let uu___351_20875 = env3 in
                                               {
                                                 bindings =
                                                   (uu___351_20875.bindings);
                                                 depth =
                                                   (uu___351_20875.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___351_20875.warn);
                                                 cache =
                                                   (uu___351_20875.cache);
                                                 nolabels =
                                                   (uu___351_20875.nolabels);
                                                 use_zfuel_name =
                                                   (uu___351_20875.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___351_20875.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___351_20875.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20813 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20890 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20890
                                         then
                                           let uu____20891 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20892 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20893 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20891 uu____20892
                                             uu____20893
                                         else ());
                                        (let uu____20895 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20895 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20932 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20932
                                               then
                                                 let uu____20933 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20934 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20935 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20936 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20933 uu____20934
                                                   uu____20935 uu____20936
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20940 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20940 with
                                               | (vars,guards,env'1,binder_decls,uu____20971)
                                                   ->
                                                   let decl_g =
                                                     let uu____20985 =
                                                       let uu____20996 =
                                                         let uu____20999 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20999 in
                                                       (g, uu____20996,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20985 in
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
                                                     let uu____21024 =
                                                       let uu____21031 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21031) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21024 in
                                                   let gsapp =
                                                     let uu____21041 =
                                                       let uu____21048 =
                                                         let uu____21051 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21051 ::
                                                           vars_tm in
                                                       (g, uu____21048) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21041 in
                                                   let gmax =
                                                     let uu____21057 =
                                                       let uu____21064 =
                                                         let uu____21067 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21067 ::
                                                           vars_tm in
                                                       (g, uu____21064) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21057 in
                                                   let body1 =
                                                     let uu____21073 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21073
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21075 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21075 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21093 =
                                                            let uu____21100 =
                                                              let uu____21101
                                                                =
                                                                let uu____21116
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
                                                                  uu____21116) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21101 in
                                                            let uu____21137 =
                                                              let uu____21140
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21140 in
                                                            (uu____21100,
                                                              uu____21137,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21093 in
                                                        let eqn_f =
                                                          let uu____21144 =
                                                            let uu____21151 =
                                                              let uu____21152
                                                                =
                                                                let uu____21163
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21163) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21152 in
                                                            (uu____21151,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21144 in
                                                        let eqn_g' =
                                                          let uu____21177 =
                                                            let uu____21184 =
                                                              let uu____21185
                                                                =
                                                                let uu____21196
                                                                  =
                                                                  let uu____21197
                                                                    =
                                                                    let uu____21202
                                                                    =
                                                                    let uu____21203
                                                                    =
                                                                    let uu____21210
                                                                    =
                                                                    let uu____21213
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21213
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21210) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21203 in
                                                                    (gsapp,
                                                                    uu____21202) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21197 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21196) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21185 in
                                                            (uu____21184,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21177 in
                                                        let uu____21236 =
                                                          let uu____21245 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21245
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21274)
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
                                                                  let uu____21299
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21299
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21304
                                                                  =
                                                                  let uu____21311
                                                                    =
                                                                    let uu____21312
                                                                    =
                                                                    let uu____21323
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21323) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21312 in
                                                                  (uu____21311,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21304 in
                                                              let uu____21344
                                                                =
                                                                let uu____21351
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21351
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21364
                                                                    =
                                                                    let uu____21367
                                                                    =
                                                                    let uu____21368
                                                                    =
                                                                    let uu____21375
                                                                    =
                                                                    let uu____21376
                                                                    =
                                                                    let uu____21387
                                                                    =
                                                                    let uu____21388
                                                                    =
                                                                    let uu____21393
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21393,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21388 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21387) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21376 in
                                                                    (uu____21375,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21368 in
                                                                    [uu____21367] in
                                                                    (d3,
                                                                    uu____21364) in
                                                              (match uu____21344
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21236
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
                            let uu____21458 =
                              let uu____21471 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21550  ->
                                   fun uu____21551  ->
                                     match (uu____21550, uu____21551) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21706 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21706 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21471 in
                            (match uu____21458 with
                             | (decls2,eqns,env01) ->
                                 let uu____21779 =
                                   let isDeclFun uu___317_21791 =
                                     match uu___317_21791 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21792 -> true
                                     | uu____21803 -> false in
                                   let uu____21804 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21804
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21779 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21844 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___318_21848  ->
                                 match uu___318_21848 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21849 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21855 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21855))) in
                      if uu____21844
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
                   let uu____21907 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21907
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
        let uu____21956 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21956 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21960 = encode_sigelt' env se in
      match uu____21960 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21976 =
                  let uu____21977 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21977 in
                [uu____21976]
            | uu____21978 ->
                let uu____21979 =
                  let uu____21982 =
                    let uu____21983 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21983 in
                  uu____21982 :: g in
                let uu____21984 =
                  let uu____21987 =
                    let uu____21988 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21988 in
                  [uu____21987] in
                FStar_List.append uu____21979 uu____21984 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22001 =
          let uu____22002 = FStar_Syntax_Subst.compress t in
          uu____22002.FStar_Syntax_Syntax.n in
        match uu____22001 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22006)) -> s = "opaque_to_smt"
        | uu____22007 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22012 =
          let uu____22013 = FStar_Syntax_Subst.compress t in
          uu____22013.FStar_Syntax_Syntax.n in
        match uu____22012 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22017)) -> s = "uninterpreted_by_smt"
        | uu____22018 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22023 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22028 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22031 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22034 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22049 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22053 =
            let uu____22054 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22054 Prims.op_Negation in
          if uu____22053
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22080 ->
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
               let uu____22100 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22100 with
               | (aname,atok,env2) ->
                   let uu____22116 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22116 with
                    | (formals,uu____22134) ->
                        let uu____22147 =
                          let uu____22152 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22152 env2 in
                        (match uu____22147 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22164 =
                                 let uu____22165 =
                                   let uu____22176 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22192  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22176,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22165 in
                               [uu____22164;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22205 =
                               let aux uu____22257 uu____22258 =
                                 match (uu____22257, uu____22258) with
                                 | ((bv,uu____22310),(env3,acc_sorts,acc)) ->
                                     let uu____22348 = gen_term_var env3 bv in
                                     (match uu____22348 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22205 with
                              | (uu____22420,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22443 =
                                      let uu____22450 =
                                        let uu____22451 =
                                          let uu____22462 =
                                            let uu____22463 =
                                              let uu____22468 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22468) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22463 in
                                          ([[app]], xs_sorts, uu____22462) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22451 in
                                      (uu____22450,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22443 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22488 =
                                      let uu____22495 =
                                        let uu____22496 =
                                          let uu____22507 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22507) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22496 in
                                      (uu____22495,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22488 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22526 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22526 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22554,uu____22555)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22556 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22556 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22573,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22579 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___319_22583  ->
                      match uu___319_22583 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22584 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22589 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22590 -> false)) in
            Prims.op_Negation uu____22579 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22599 =
               let uu____22606 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22606 env fv t quals in
             match uu____22599 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22621 =
                   let uu____22624 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22624 in
                 (uu____22621, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22632 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22632 with
           | (uu____22641,f1) ->
               let uu____22643 = encode_formula f1 env in
               (match uu____22643 with
                | (f2,decls) ->
                    let g =
                      let uu____22657 =
                        let uu____22658 =
                          let uu____22665 =
                            let uu____22668 =
                              let uu____22669 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22669 in
                            FStar_Pervasives_Native.Some uu____22668 in
                          let uu____22670 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22665, uu____22670) in
                        FStar_SMTEncoding_Util.mkAssume uu____22658 in
                      [uu____22657] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22676) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22688 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22706 =
                       let uu____22709 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22709.FStar_Syntax_Syntax.fv_name in
                     uu____22706.FStar_Syntax_Syntax.v in
                   let uu____22710 =
                     let uu____22711 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22711 in
                   if uu____22710
                   then
                     let val_decl =
                       let uu___354_22739 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___354_22739.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___354_22739.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___354_22739.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22744 = encode_sigelt' env1 val_decl in
                     match uu____22744 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22688 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22772,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22774;
                          FStar_Syntax_Syntax.lbtyp = uu____22775;
                          FStar_Syntax_Syntax.lbeff = uu____22776;
                          FStar_Syntax_Syntax.lbdef = uu____22777;_}::[]),uu____22778)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22797 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22797 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22826 =
                   let uu____22829 =
                     let uu____22830 =
                       let uu____22837 =
                         let uu____22838 =
                           let uu____22849 =
                             let uu____22850 =
                               let uu____22855 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22855) in
                             FStar_SMTEncoding_Util.mkEq uu____22850 in
                           ([[b2t_x]], [xx], uu____22849) in
                         FStar_SMTEncoding_Util.mkForall uu____22838 in
                       (uu____22837,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22830 in
                   [uu____22829] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22826 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22888,uu____22889) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___320_22898  ->
                  match uu___320_22898 with
                  | FStar_Syntax_Syntax.Discriminator uu____22899 -> true
                  | uu____22900 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22903,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22914 =
                     let uu____22915 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22915.FStar_Ident.idText in
                   uu____22914 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___321_22919  ->
                     match uu___321_22919 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22920 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22924) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___322_22941  ->
                  match uu___322_22941 with
                  | FStar_Syntax_Syntax.Projector uu____22942 -> true
                  | uu____22947 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22950 = try_lookup_free_var env l in
          (match uu____22950 with
           | FStar_Pervasives_Native.Some uu____22957 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___355_22961 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___355_22961.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___355_22961.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___355_22961.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22968) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22986) ->
          let uu____22995 = encode_sigelts env ses in
          (match uu____22995 with
           | (g,env1) ->
               let uu____23012 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___323_23035  ->
                         match uu___323_23035 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23036;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23037;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23038;_}
                             -> false
                         | uu____23041 -> true)) in
               (match uu____23012 with
                | (g',inversions) ->
                    let uu____23056 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___324_23077  ->
                              match uu___324_23077 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23078 ->
                                  true
                              | uu____23089 -> false)) in
                    (match uu____23056 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23107,tps,k,uu____23110,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___325_23127  ->
                    match uu___325_23127 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23128 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23137 = c in
              match uu____23137 with
              | (name,args,uu____23142,uu____23143,uu____23144) ->
                  let uu____23149 =
                    let uu____23150 =
                      let uu____23161 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23178  ->
                                match uu____23178 with
                                | (uu____23185,sort,uu____23187) -> sort)) in
                      (name, uu____23161, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23150 in
                  [uu____23149]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23214 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23220 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23220 FStar_Option.isNone)) in
            if uu____23214
            then []
            else
              (let uu____23252 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23252 with
               | (xxsym,xx) ->
                   let uu____23261 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23300  ->
                             fun l  ->
                               match uu____23300 with
                               | (out,decls) ->
                                   let uu____23320 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23320 with
                                    | (uu____23331,data_t) ->
                                        let uu____23333 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23333 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23379 =
                                                 let uu____23380 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23380.FStar_Syntax_Syntax.n in
                                               match uu____23379 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23391,indices) ->
                                                   indices
                                               | uu____23413 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23437  ->
                                                         match uu____23437
                                                         with
                                                         | (x,uu____23443) ->
                                                             let uu____23444
                                                               =
                                                               let uu____23445
                                                                 =
                                                                 let uu____23452
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23452,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23445 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23444)
                                                    env) in
                                             let uu____23455 =
                                               encode_args indices env1 in
                                             (match uu____23455 with
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
                                                      let uu____23481 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23497
                                                                 =
                                                                 let uu____23502
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23502,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23497)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23481
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23505 =
                                                      let uu____23506 =
                                                        let uu____23511 =
                                                          let uu____23512 =
                                                            let uu____23517 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23517,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23512 in
                                                        (out, uu____23511) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23506 in
                                                    (uu____23505,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23261 with
                    | (data_ax,decls) ->
                        let uu____23530 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23530 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23541 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23541 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23545 =
                                 let uu____23552 =
                                   let uu____23553 =
                                     let uu____23564 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23579 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23564,
                                       uu____23579) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23553 in
                                 let uu____23594 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23552,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23594) in
                               FStar_SMTEncoding_Util.mkAssume uu____23545 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23597 =
            let uu____23610 =
              let uu____23611 = FStar_Syntax_Subst.compress k in
              uu____23611.FStar_Syntax_Syntax.n in
            match uu____23610 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23656 -> (tps, k) in
          (match uu____23597 with
           | (formals,res) ->
               let uu____23679 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23679 with
                | (formals1,res1) ->
                    let uu____23690 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23690 with
                     | (vars,guards,env',binder_decls,uu____23715) ->
                         let uu____23728 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23728 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23747 =
                                  let uu____23754 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23754) in
                                FStar_SMTEncoding_Util.mkApp uu____23747 in
                              let uu____23763 =
                                let tname_decl =
                                  let uu____23773 =
                                    let uu____23774 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23806  ->
                                              match uu____23806 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23819 = varops.next_id () in
                                    (tname, uu____23774,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23819, false) in
                                  constructor_or_logic_type_decl uu____23773 in
                                let uu____23828 =
                                  match vars with
                                  | [] ->
                                      let uu____23841 =
                                        let uu____23842 =
                                          let uu____23845 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23845 in
                                        push_free_var env1 t tname
                                          uu____23842 in
                                      ([], uu____23841)
                                  | uu____23852 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23861 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23861 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23875 =
                                          let uu____23882 =
                                            let uu____23883 =
                                              let uu____23898 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23898) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23883 in
                                          (uu____23882,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23875 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23828 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23763 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23938 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23938 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23956 =
                                               let uu____23957 =
                                                 let uu____23964 =
                                                   let uu____23965 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23965 in
                                                 (uu____23964,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23957 in
                                             [uu____23956]
                                           else [] in
                                         let uu____23969 =
                                           let uu____23972 =
                                             let uu____23975 =
                                               let uu____23976 =
                                                 let uu____23983 =
                                                   let uu____23984 =
                                                     let uu____23995 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23995) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23984 in
                                                 (uu____23983,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23976 in
                                             [uu____23975] in
                                           FStar_List.append karr uu____23972 in
                                         FStar_List.append decls1 uu____23969 in
                                   let aux =
                                     let uu____24011 =
                                       let uu____24014 =
                                         inversion_axioms tapp vars in
                                       let uu____24017 =
                                         let uu____24020 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24020] in
                                       FStar_List.append uu____24014
                                         uu____24017 in
                                     FStar_List.append kindingAx uu____24011 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24027,uu____24028,uu____24029,uu____24030,uu____24031)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24039,t,uu____24041,n_tps,uu____24043) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24051 = new_term_constant_and_tok_from_lid env d in
          (match uu____24051 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24068 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24068 with
                | (formals,t_res) ->
                    let uu____24103 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24103 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24117 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24117 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24187 =
                                            mk_term_projector_name d x in
                                          (uu____24187,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24189 =
                                  let uu____24208 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24208, true) in
                                FStar_All.pipe_right uu____24189
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
                              let uu____24247 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24247 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24259::uu____24260 ->
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
                                         let uu____24305 =
                                           let uu____24316 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24316) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24305
                                     | uu____24341 -> tok_typing in
                                   let uu____24350 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24350 with
                                    | (vars',guards',env'',decls_formals,uu____24375)
                                        ->
                                        let uu____24388 =
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
                                        (match uu____24388 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24419 ->
                                                   let uu____24426 =
                                                     let uu____24427 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24427 in
                                                   [uu____24426] in
                                             let encode_elim uu____24437 =
                                               let uu____24438 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24438 with
                                               | (head1,args) ->
                                                   let uu____24481 =
                                                     let uu____24482 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24482.FStar_Syntax_Syntax.n in
                                                   (match uu____24481 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24492;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24493;_},uu____24494)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24500 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24500
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
                                                                 | uu____24543
                                                                    ->
                                                                    let uu____24544
                                                                    =
                                                                    let uu____24545
                                                                    =
                                                                    let uu____24550
                                                                    =
                                                                    let uu____24551
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24551 in
                                                                    (uu____24550,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24545 in
                                                                    FStar_Exn.raise
                                                                    uu____24544 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24567
                                                                    =
                                                                    let uu____24568
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24568 in
                                                                    if
                                                                    uu____24567
                                                                    then
                                                                    let uu____24581
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24581]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24583
                                                               =
                                                               let uu____24596
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24646
                                                                     ->
                                                                    fun
                                                                    uu____24647
                                                                     ->
                                                                    match 
                                                                    (uu____24646,
                                                                    uu____24647)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24742
                                                                    =
                                                                    let uu____24749
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24749 in
                                                                    (match uu____24742
                                                                    with
                                                                    | 
                                                                    (uu____24762,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24770
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24770
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24772
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24772
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
                                                                 uu____24596 in
                                                             (match uu____24583
                                                              with
                                                              | (uu____24787,arg_vars,elim_eqns_or_guards,uu____24790)
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
                                                                    let uu____24820
                                                                    =
                                                                    let uu____24827
                                                                    =
                                                                    let uu____24828
                                                                    =
                                                                    let uu____24839
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24850
                                                                    =
                                                                    let uu____24851
                                                                    =
                                                                    let uu____24856
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24856) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24851 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24839,
                                                                    uu____24850) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24828 in
                                                                    (uu____24827,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24820 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24879
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24879,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24881
                                                                    =
                                                                    let uu____24888
                                                                    =
                                                                    let uu____24889
                                                                    =
                                                                    let uu____24900
                                                                    =
                                                                    let uu____24905
                                                                    =
                                                                    let uu____24908
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24908] in
                                                                    [uu____24905] in
                                                                    let uu____24913
                                                                    =
                                                                    let uu____24914
                                                                    =
                                                                    let uu____24919
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24920
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24919,
                                                                    uu____24920) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24914 in
                                                                    (uu____24900,
                                                                    [x],
                                                                    uu____24913) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24889 in
                                                                    let uu____24939
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24888,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24939) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24881
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24946
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
                                                                    (let uu____24974
                                                                    =
                                                                    let uu____24975
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24975
                                                                    dapp1 in
                                                                    [uu____24974]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24946
                                                                    FStar_List.flatten in
                                                                    let uu____24982
                                                                    =
                                                                    let uu____24989
                                                                    =
                                                                    let uu____24990
                                                                    =
                                                                    let uu____25001
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25012
                                                                    =
                                                                    let uu____25013
                                                                    =
                                                                    let uu____25018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25018) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25013 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25001,
                                                                    uu____25012) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24990 in
                                                                    (uu____24989,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24982) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25039 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25039
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
                                                                 | uu____25082
                                                                    ->
                                                                    let uu____25083
                                                                    =
                                                                    let uu____25084
                                                                    =
                                                                    let uu____25089
                                                                    =
                                                                    let uu____25090
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25090 in
                                                                    (uu____25089,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25084 in
                                                                    FStar_Exn.raise
                                                                    uu____25083 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25106
                                                                    =
                                                                    let uu____25107
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25107 in
                                                                    if
                                                                    uu____25106
                                                                    then
                                                                    let uu____25120
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25120]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25122
                                                               =
                                                               let uu____25135
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25185
                                                                     ->
                                                                    fun
                                                                    uu____25186
                                                                     ->
                                                                    match 
                                                                    (uu____25185,
                                                                    uu____25186)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25281
                                                                    =
                                                                    let uu____25288
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25288 in
                                                                    (match uu____25281
                                                                    with
                                                                    | 
                                                                    (uu____25301,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25309
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25309
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25311
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25311
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
                                                                 uu____25135 in
                                                             (match uu____25122
                                                              with
                                                              | (uu____25326,arg_vars,elim_eqns_or_guards,uu____25329)
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
                                                                    let uu____25359
                                                                    =
                                                                    let uu____25366
                                                                    =
                                                                    let uu____25367
                                                                    =
                                                                    let uu____25378
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25389
                                                                    =
                                                                    let uu____25390
                                                                    =
                                                                    let uu____25395
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25395) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25390 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25378,
                                                                    uu____25389) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25367 in
                                                                    (uu____25366,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25359 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25418
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25418,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25420
                                                                    =
                                                                    let uu____25427
                                                                    =
                                                                    let uu____25428
                                                                    =
                                                                    let uu____25439
                                                                    =
                                                                    let uu____25444
                                                                    =
                                                                    let uu____25447
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25447] in
                                                                    [uu____25444] in
                                                                    let uu____25452
                                                                    =
                                                                    let uu____25453
                                                                    =
                                                                    let uu____25458
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25459
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25458,
                                                                    uu____25459) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25453 in
                                                                    (uu____25439,
                                                                    [x],
                                                                    uu____25452) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25428 in
                                                                    let uu____25478
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25427,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25478) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25420
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25485
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
                                                                    (let uu____25513
                                                                    =
                                                                    let uu____25514
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25514
                                                                    dapp1 in
                                                                    [uu____25513]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25485
                                                                    FStar_List.flatten in
                                                                    let uu____25521
                                                                    =
                                                                    let uu____25528
                                                                    =
                                                                    let uu____25529
                                                                    =
                                                                    let uu____25540
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25551
                                                                    =
                                                                    let uu____25552
                                                                    =
                                                                    let uu____25557
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25557) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25552 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25540,
                                                                    uu____25551) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25529 in
                                                                    (uu____25528,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25521) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25576 ->
                                                        ((let uu____25578 =
                                                            let uu____25579 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25580 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25579
                                                              uu____25580 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25578);
                                                         ([], []))) in
                                             let uu____25585 = encode_elim () in
                                             (match uu____25585 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25605 =
                                                      let uu____25608 =
                                                        let uu____25611 =
                                                          let uu____25614 =
                                                            let uu____25617 =
                                                              let uu____25618
                                                                =
                                                                let uu____25629
                                                                  =
                                                                  let uu____25632
                                                                    =
                                                                    let uu____25633
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25633 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25632 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25629) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25618 in
                                                            [uu____25617] in
                                                          let uu____25638 =
                                                            let uu____25641 =
                                                              let uu____25644
                                                                =
                                                                let uu____25647
                                                                  =
                                                                  let uu____25650
                                                                    =
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25656
                                                                    =
                                                                    let uu____25657
                                                                    =
                                                                    let uu____25664
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    let uu____25676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25676) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25665 in
                                                                    (uu____25664,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25657 in
                                                                    let uu____25689
                                                                    =
                                                                    let uu____25692
                                                                    =
                                                                    let uu____25693
                                                                    =
                                                                    let uu____25700
                                                                    =
                                                                    let uu____25701
                                                                    =
                                                                    let uu____25712
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25723
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25712,
                                                                    uu____25723) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25701 in
                                                                    (uu____25700,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25693 in
                                                                    [uu____25692] in
                                                                    uu____25656
                                                                    ::
                                                                    uu____25689 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25653 in
                                                                  FStar_List.append
                                                                    uu____25650
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25647 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25644 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25641 in
                                                          FStar_List.append
                                                            uu____25614
                                                            uu____25638 in
                                                        FStar_List.append
                                                          decls3 uu____25611 in
                                                      FStar_List.append
                                                        decls2 uu____25608 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25605 in
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
           (fun uu____25769  ->
              fun se  ->
                match uu____25769 with
                | (g,env1) ->
                    let uu____25789 = encode_sigelt env1 se in
                    (match uu____25789 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25846 =
        match uu____25846 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25878 ->
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
                 ((let uu____25884 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25884
                   then
                     let uu____25885 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25886 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25887 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25885 uu____25886 uu____25887
                   else ());
                  (let uu____25889 = encode_term t1 env1 in
                   match uu____25889 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25905 =
                         let uu____25912 =
                           let uu____25913 =
                             let uu____25914 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25914
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25913 in
                         new_term_constant_from_string env1 x uu____25912 in
                       (match uu____25905 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25930 = FStar_Options.log_queries () in
                              if uu____25930
                              then
                                let uu____25933 =
                                  let uu____25934 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25935 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25936 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25934 uu____25935 uu____25936 in
                                FStar_Pervasives_Native.Some uu____25933
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25952,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25966 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25966 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25989,se,uu____25991) ->
                 let uu____25996 = encode_sigelt env1 se in
                 (match uu____25996 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26013,se) ->
                 let uu____26019 = encode_sigelt env1 se in
                 (match uu____26019 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26036 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26036 with | (uu____26059,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26071 'Auu____26072 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26072,'Auu____26071)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26140  ->
              match uu____26140 with
              | (l,uu____26152,uu____26153) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26199  ->
              match uu____26199 with
              | (l,uu____26213,uu____26214) ->
                  let uu____26223 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26224 =
                    let uu____26227 =
                      let uu____26228 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26228 in
                    [uu____26227] in
                  uu____26223 :: uu____26224)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26249 =
      let uu____26252 =
        let uu____26253 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26256 =
          let uu____26257 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26257 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26253;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26256
        } in
      [uu____26252] in
    FStar_ST.op_Colon_Equals last_env uu____26249
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26316 = FStar_ST.op_Bang last_env in
      match uu____26316 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26372 ->
          let uu___356_26375 = e in
          let uu____26376 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___356_26375.bindings);
            depth = (uu___356_26375.depth);
            tcenv;
            warn = (uu___356_26375.warn);
            cache = (uu___356_26375.cache);
            nolabels = (uu___356_26375.nolabels);
            use_zfuel_name = (uu___356_26375.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___356_26375.encode_non_total_function_typ);
            current_module_name = uu____26376
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26380 = FStar_ST.op_Bang last_env in
    match uu____26380 with
    | [] -> failwith "Empty env stack"
    | uu____26435::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26493  ->
    let uu____26494 = FStar_ST.op_Bang last_env in
    match uu____26494 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___357_26557 = hd1 in
          {
            bindings = (uu___357_26557.bindings);
            depth = (uu___357_26557.depth);
            tcenv = (uu___357_26557.tcenv);
            warn = (uu___357_26557.warn);
            cache = refs;
            nolabels = (uu___357_26557.nolabels);
            use_zfuel_name = (uu___357_26557.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___357_26557.encode_non_total_function_typ);
            current_module_name = (uu___357_26557.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26612  ->
    let uu____26613 = FStar_ST.op_Bang last_env in
    match uu____26613 with
    | [] -> failwith "Popping an empty stack"
    | uu____26668::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26761::uu____26762,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___358_26770 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___358_26770.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___358_26770.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___358_26770.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26771 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26786 =
        let uu____26789 =
          let uu____26790 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26790 in
        let uu____26791 = open_fact_db_tags env in uu____26789 :: uu____26791 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26786
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
      let uu____26813 = encode_sigelt env se in
      match uu____26813 with
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
        let uu____26849 = FStar_Options.log_queries () in
        if uu____26849
        then
          let uu____26852 =
            let uu____26853 =
              let uu____26854 =
                let uu____26855 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26855 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26854 in
            FStar_SMTEncoding_Term.Caption uu____26853 in
          uu____26852 :: decls
        else decls in
      (let uu____26866 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26866
       then
         let uu____26867 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26867
       else ());
      (let env =
         let uu____26870 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26870 tcenv in
       let uu____26871 = encode_top_level_facts env se in
       match uu____26871 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26885 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26885)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26897 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26897
       then
         let uu____26898 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26898
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26933  ->
                 fun se  ->
                   match uu____26933 with
                   | (g,env2) ->
                       let uu____26953 = encode_top_level_facts env2 se in
                       (match uu____26953 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26976 =
         encode_signature
           (let uu___359_26985 = env in
            {
              bindings = (uu___359_26985.bindings);
              depth = (uu___359_26985.depth);
              tcenv = (uu___359_26985.tcenv);
              warn = false;
              cache = (uu___359_26985.cache);
              nolabels = (uu___359_26985.nolabels);
              use_zfuel_name = (uu___359_26985.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___359_26985.encode_non_total_function_typ);
              current_module_name = (uu___359_26985.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26976 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27002 = FStar_Options.log_queries () in
             if uu____27002
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___360_27010 = env1 in
               {
                 bindings = (uu___360_27010.bindings);
                 depth = (uu___360_27010.depth);
                 tcenv = (uu___360_27010.tcenv);
                 warn = true;
                 cache = (uu___360_27010.cache);
                 nolabels = (uu___360_27010.nolabels);
                 use_zfuel_name = (uu___360_27010.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___360_27010.encode_non_total_function_typ);
                 current_module_name = (uu___360_27010.current_module_name)
               });
            (let uu____27012 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27012
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
        (let uu____27064 =
           let uu____27065 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27065.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27064);
        (let env =
           let uu____27067 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27067 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27079 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27114 = aux rest in
                 (match uu____27114 with
                  | (out,rest1) ->
                      let t =
                        let uu____27144 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27144 with
                        | FStar_Pervasives_Native.Some uu____27149 ->
                            let uu____27150 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27150
                              x.FStar_Syntax_Syntax.sort
                        | uu____27151 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27155 =
                        let uu____27158 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___361_27161 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___361_27161.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___361_27161.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27158 :: out in
                      (uu____27155, rest1))
             | uu____27166 -> ([], bindings1) in
           let uu____27173 = aux bindings in
           match uu____27173 with
           | (closing,bindings1) ->
               let uu____27198 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27198, bindings1) in
         match uu____27079 with
         | (q1,bindings1) ->
             let uu____27221 =
               let uu____27226 =
                 FStar_List.filter
                   (fun uu___326_27231  ->
                      match uu___326_27231 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27232 ->
                          false
                      | uu____27239 -> true) bindings1 in
               encode_env_bindings env uu____27226 in
             (match uu____27221 with
              | (env_decls,env1) ->
                  ((let uu____27257 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27257
                    then
                      let uu____27258 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27258
                    else ());
                   (let uu____27260 = encode_formula q1 env1 in
                    match uu____27260 with
                    | (phi,qdecls) ->
                        let uu____27281 =
                          let uu____27286 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27286 phi in
                        (match uu____27281 with
                         | (labels,phi1) ->
                             let uu____27303 = encode_labels labels in
                             (match uu____27303 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27340 =
                                      let uu____27347 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27348 =
                                        varops.mk_unique "@query" in
                                      (uu____27347,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27348) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27340 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))