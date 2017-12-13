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
      (fun uu___309_107  ->
         match uu___309_107 with
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
        let uu___332_205 = a in
        let uu____206 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____206;
          FStar_Syntax_Syntax.index =
            (uu___332_205.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___332_205.FStar_Syntax_Syntax.sort)
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
    let uu___333_1869 = x in
    let uu____1870 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1870;
      FStar_Syntax_Syntax.index = (uu___333_1869.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___333_1869.FStar_Syntax_Syntax.sort)
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
                 (fun uu___310_2317  ->
                    match uu___310_2317 with
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
           (fun uu___311_2340  ->
              match uu___311_2340 with
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
        (let uu___334_2420 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___334_2420.tcenv);
           warn = (uu___334_2420.warn);
           cache = (uu___334_2420.cache);
           nolabels = (uu___334_2420.nolabels);
           use_zfuel_name = (uu___334_2420.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___334_2420.encode_non_total_function_typ);
           current_module_name = (uu___334_2420.current_module_name)
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
        (let uu___335_2438 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___335_2438.depth);
           tcenv = (uu___335_2438.tcenv);
           warn = (uu___335_2438.warn);
           cache = (uu___335_2438.cache);
           nolabels = (uu___335_2438.nolabels);
           use_zfuel_name = (uu___335_2438.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___335_2438.encode_non_total_function_typ);
           current_module_name = (uu___335_2438.current_module_name)
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
          (let uu___336_2459 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___336_2459.depth);
             tcenv = (uu___336_2459.tcenv);
             warn = (uu___336_2459.warn);
             cache = (uu___336_2459.cache);
             nolabels = (uu___336_2459.nolabels);
             use_zfuel_name = (uu___336_2459.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___336_2459.encode_non_total_function_typ);
             current_module_name = (uu___336_2459.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___337_2469 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___337_2469.depth);
          tcenv = (uu___337_2469.tcenv);
          warn = (uu___337_2469.warn);
          cache = (uu___337_2469.cache);
          nolabels = (uu___337_2469.nolabels);
          use_zfuel_name = (uu___337_2469.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___337_2469.encode_non_total_function_typ);
          current_module_name = (uu___337_2469.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___312_2493  ->
             match uu___312_2493 with
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
        let uu___338_2564 = env in
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
          depth = (uu___338_2564.depth);
          tcenv = (uu___338_2564.tcenv);
          warn = (uu___338_2564.warn);
          cache = (uu___338_2564.cache);
          nolabels = (uu___338_2564.nolabels);
          use_zfuel_name = (uu___338_2564.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___338_2564.encode_non_total_function_typ);
          current_module_name = (uu___338_2564.current_module_name)
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
        (fun uu___313_2627  ->
           match uu___313_2627 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2666 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2683 =
        lookup_binding env
          (fun uu___314_2691  ->
             match uu___314_2691 with
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
          let uu___339_2807 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___339_2807.depth);
            tcenv = (uu___339_2807.tcenv);
            warn = (uu___339_2807.warn);
            cache = (uu___339_2807.cache);
            nolabels = (uu___339_2807.nolabels);
            use_zfuel_name = (uu___339_2807.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___339_2807.encode_non_total_function_typ);
            current_module_name = (uu___339_2807.current_module_name)
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
            let uu___340_2859 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___340_2859.depth);
              tcenv = (uu___340_2859.tcenv);
              warn = (uu___340_2859.warn);
              cache = (uu___340_2859.cache);
              nolabels = (uu___340_2859.nolabels);
              use_zfuel_name = (uu___340_2859.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___340_2859.encode_non_total_function_typ);
              current_module_name = (uu___340_2859.current_module_name)
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
        (fun uu___315_3103  ->
           match uu___315_3103 with
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
               (fun uu___316_3422  ->
                  match uu___316_3422 with
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
  fun uu___317_3520  ->
    match uu___317_3520 with
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
          let uu____4357 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4357, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4360 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4360, [])
      | FStar_Const.Const_char c1 ->
          let uu____4364 =
            let uu____4365 =
              let uu____4372 =
                let uu____4375 =
                  let uu____4376 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4376 in
                [uu____4375] in
              ("FStar.Char.__char_of_int", uu____4372) in
            FStar_SMTEncoding_Util.mkApp uu____4365 in
          (uu____4364, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4392 =
            let uu____4393 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4393 in
          (uu____4392, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4414) ->
          let uu____4415 = varops.string_const s in (uu____4415, [])
      | FStar_Const.Const_range uu____4418 ->
          let uu____4419 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4419, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4425 =
            let uu____4426 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4426 in
          failwith uu____4425
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
        (let uu____4455 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4455
         then
           let uu____4456 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4456
         else ());
        (let uu____4458 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4542  ->
                   fun b  ->
                     match uu____4542 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4621 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4637 = gen_term_var env1 x in
                           match uu____4637 with
                           | (xxsym,xx,env') ->
                               let uu____4661 =
                                 let uu____4666 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4666 env1 xx in
                               (match uu____4661 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4621 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4458 with
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
          let uu____4825 = encode_term t env in
          match uu____4825 with
          | (t1,decls) ->
              let uu____4836 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4836, decls)
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
          let uu____4847 = encode_term t env in
          match uu____4847 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4862 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4862, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4864 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4864, decls))
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
        let uu____4870 = encode_args args_e env in
        match uu____4870 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4889 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4898 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4898 in
            let binary arg_tms1 =
              let uu____4911 =
                let uu____4912 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4912 in
              let uu____4913 =
                let uu____4914 =
                  let uu____4915 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4915 in
                FStar_SMTEncoding_Term.unboxInt uu____4914 in
              (uu____4911, uu____4913) in
            let mk_default uu____4921 =
              let uu____4922 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4922 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4973 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4973
              then
                let uu____4974 = let uu____4975 = mk_args ts in op uu____4975 in
                FStar_All.pipe_right uu____4974 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5004 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5004
              then
                let uu____5005 = binary ts in
                match uu____5005 with
                | (t1,t2) ->
                    let uu____5012 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5012
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5016 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5016
                 then
                   let uu____5017 = op (binary ts) in
                   FStar_All.pipe_right uu____5017
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
            let uu____5148 =
              let uu____5157 =
                FStar_List.tryFind
                  (fun uu____5179  ->
                     match uu____5179 with
                     | (l,uu____5189) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5157 FStar_Util.must in
            (match uu____5148 with
             | (uu____5228,op) ->
                 let uu____5238 = op arg_tms in (uu____5238, decls))
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
        let uu____5246 = FStar_List.hd args_e in
        match uu____5246 with
        | (tm_sz,uu____5254) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5264 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5264 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5272 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5272);
                   t_decls) in
            let uu____5273 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5293::(sz_arg,uu____5295)::uu____5296::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5345 =
                    let uu____5348 = FStar_List.tail args_e in
                    FStar_List.tail uu____5348 in
                  let uu____5351 =
                    let uu____5354 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5354 in
                  (uu____5345, uu____5351)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5360::(sz_arg,uu____5362)::uu____5363::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5412 =
                    let uu____5413 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5413 in
                  failwith uu____5412
              | uu____5422 ->
                  let uu____5429 = FStar_List.tail args_e in
                  (uu____5429, FStar_Pervasives_Native.None) in
            (match uu____5273 with
             | (arg_tms,ext_sz) ->
                 let uu____5452 = encode_args arg_tms env in
                 (match uu____5452 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5473 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5482 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5482 in
                      let unary_arith arg_tms2 =
                        let uu____5491 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5491 in
                      let binary arg_tms2 =
                        let uu____5504 =
                          let uu____5505 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5505 in
                        let uu____5506 =
                          let uu____5507 =
                            let uu____5508 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5508 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5507 in
                        (uu____5504, uu____5506) in
                      let binary_arith arg_tms2 =
                        let uu____5523 =
                          let uu____5524 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5524 in
                        let uu____5525 =
                          let uu____5526 =
                            let uu____5527 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5527 in
                          FStar_SMTEncoding_Term.unboxInt uu____5526 in
                        (uu____5523, uu____5525) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5576 =
                          let uu____5577 = mk_args ts in op uu____5577 in
                        FStar_All.pipe_right uu____5576 resBox in
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
                        let uu____5685 =
                          let uu____5688 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5688 in
                        let uu____5690 =
                          let uu____5693 =
                            let uu____5694 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5694 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5693 in
                        mk_bv uu____5685 unary uu____5690 arg_tms2 in
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
                      let uu____5893 =
                        let uu____5902 =
                          FStar_List.tryFind
                            (fun uu____5924  ->
                               match uu____5924 with
                               | (l,uu____5934) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5902 FStar_Util.must in
                      (match uu____5893 with
                       | (uu____5975,op) ->
                           let uu____5985 = op arg_tms1 in
                           (uu____5985, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5996 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5996
       then
         let uu____5997 = FStar_Syntax_Print.tag_of_term t in
         let uu____5998 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5999 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5997 uu____5998
           uu____5999
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6005 ->
           let uu____6030 =
             let uu____6031 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6032 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6033 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6034 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6031
               uu____6032 uu____6033 uu____6034 in
           failwith uu____6030
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6039 =
             let uu____6040 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6041 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6042 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6043 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6040
               uu____6041 uu____6042 uu____6043 in
           failwith uu____6039
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6049 =
             let uu____6050 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6050 in
           failwith uu____6049
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6057) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6098;
              FStar_Syntax_Syntax.vars = uu____6099;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6116 = varops.fresh "t" in
             (uu____6116, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6119 =
               let uu____6130 =
                 let uu____6133 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6133 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6130) in
             FStar_SMTEncoding_Term.DeclFun uu____6119 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6141) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6151 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6151, [])
       | FStar_Syntax_Syntax.Tm_type uu____6154 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6158) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6183 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6183 with
            | (binders1,res) ->
                let uu____6194 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6194
                then
                  let uu____6199 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6199 with
                   | (vars,guards,env',decls,uu____6224) ->
                       let fsym =
                         let uu____6242 = varops.fresh "f" in
                         (uu____6242, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6245 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___341_6254 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___341_6254.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___341_6254.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___341_6254.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___341_6254.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___341_6254.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___341_6254.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___341_6254.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___341_6254.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___341_6254.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___341_6254.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___341_6254.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___341_6254.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___341_6254.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___341_6254.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___341_6254.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___341_6254.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___341_6254.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___341_6254.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___341_6254.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___341_6254.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___341_6254.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___341_6254.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___341_6254.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___341_6254.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___341_6254.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___341_6254.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___341_6254.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___341_6254.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___341_6254.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___341_6254.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___341_6254.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___341_6254.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___341_6254.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6245 with
                        | (pre_opt,res_t) ->
                            let uu____6265 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6265 with
                             | (res_pred,decls') ->
                                 let uu____6276 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6289 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6289, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6293 =
                                         encode_formula pre env' in
                                       (match uu____6293 with
                                        | (guard,decls0) ->
                                            let uu____6306 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6306, decls0)) in
                                 (match uu____6276 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6318 =
                                          let uu____6329 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6329) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6318 in
                                      let cvars =
                                        let uu____6347 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6347
                                          (FStar_List.filter
                                             (fun uu____6361  ->
                                                match uu____6361 with
                                                | (x,uu____6367) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6386 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6386 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6394 =
                                             let uu____6395 =
                                               let uu____6402 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6402) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6395 in
                                           (uu____6394,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6422 =
                                               let uu____6423 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6423 in
                                             varops.mk_unique uu____6422 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6434 =
                                               FStar_Options.log_queries () in
                                             if uu____6434
                                             then
                                               let uu____6437 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6437
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6445 =
                                               let uu____6452 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6452) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6445 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6464 =
                                               let uu____6471 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6471,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6464 in
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
                                             let uu____6492 =
                                               let uu____6499 =
                                                 let uu____6500 =
                                                   let uu____6511 =
                                                     let uu____6512 =
                                                       let uu____6517 =
                                                         let uu____6518 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6518 in
                                                       (f_has_t, uu____6517) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6512 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6511) in
                                                 mkForall_fuel uu____6500 in
                                               (uu____6499,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6492 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6541 =
                                               let uu____6548 =
                                                 let uu____6549 =
                                                   let uu____6560 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6560) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6549 in
                                               (uu____6548,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6541 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6585 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6585);
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
                     let uu____6600 =
                       let uu____6607 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6607,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6600 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6619 =
                       let uu____6626 =
                         let uu____6627 =
                           let uu____6638 =
                             let uu____6639 =
                               let uu____6644 =
                                 let uu____6645 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6645 in
                               (f_has_t, uu____6644) in
                             FStar_SMTEncoding_Util.mkImp uu____6639 in
                           ([[f_has_t]], [fsym], uu____6638) in
                         mkForall_fuel uu____6627 in
                       (uu____6626, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6619 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6672 ->
           let uu____6679 =
             let uu____6684 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6684 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6691;
                 FStar_Syntax_Syntax.vars = uu____6692;_} ->
                 let uu____6699 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6699 with
                  | (b,f1) ->
                      let uu____6724 =
                        let uu____6725 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6725 in
                      (uu____6724, f1))
             | uu____6734 -> failwith "impossible" in
           (match uu____6679 with
            | (x,f) ->
                let uu____6745 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6745 with
                 | (base_t,decls) ->
                     let uu____6756 = gen_term_var env x in
                     (match uu____6756 with
                      | (x1,xtm,env') ->
                          let uu____6770 = encode_formula f env' in
                          (match uu____6770 with
                           | (refinement,decls') ->
                               let uu____6781 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6781 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6797 =
                                        let uu____6800 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6807 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6800
                                          uu____6807 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6797 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6840  ->
                                              match uu____6840 with
                                              | (y,uu____6846) ->
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
                                    let uu____6879 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6879 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6887 =
                                           let uu____6888 =
                                             let uu____6895 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6895) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6888 in
                                         (uu____6887,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6916 =
                                             let uu____6917 =
                                               let uu____6918 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6918 in
                                             Prims.strcat module_name
                                               uu____6917 in
                                           varops.mk_unique uu____6916 in
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
                                           let uu____6932 =
                                             let uu____6939 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6939) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6932 in
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
                                           let uu____6954 =
                                             let uu____6961 =
                                               let uu____6962 =
                                                 let uu____6973 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6973) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6962 in
                                             (uu____6961,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6954 in
                                         let t_kinding =
                                           let uu____6991 =
                                             let uu____6998 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6998,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6991 in
                                         let t_interp =
                                           let uu____7016 =
                                             let uu____7023 =
                                               let uu____7024 =
                                                 let uu____7035 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7035) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7024 in
                                             let uu____7058 =
                                               let uu____7061 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7061 in
                                             (uu____7023, uu____7058,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7016 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7068 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7068);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7098 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7098 in
           let uu____7099 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7099 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7111 =
                    let uu____7118 =
                      let uu____7119 =
                        let uu____7120 =
                          let uu____7121 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7121 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7120 in
                      varops.mk_unique uu____7119 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7118) in
                  FStar_SMTEncoding_Util.mkAssume uu____7111 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7126 ->
           let uu____7141 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7141 with
            | (head1,args_e) ->
                let uu____7182 =
                  let uu____7195 =
                    let uu____7196 = FStar_Syntax_Subst.compress head1 in
                    uu____7196.FStar_Syntax_Syntax.n in
                  (uu____7195, args_e) in
                (match uu____7182 with
                 | uu____7211 when head_redex env head1 ->
                     let uu____7224 = whnf env t in
                     encode_term uu____7224 env
                 | uu____7225 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7244 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7258;
                       FStar_Syntax_Syntax.vars = uu____7259;_},uu____7260),uu____7261::
                    (v1,uu____7263)::(v2,uu____7265)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7316 = encode_term v1 env in
                     (match uu____7316 with
                      | (v11,decls1) ->
                          let uu____7327 = encode_term v2 env in
                          (match uu____7327 with
                           | (v21,decls2) ->
                               let uu____7338 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7338,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7342::(v1,uu____7344)::(v2,uu____7346)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7393 = encode_term v1 env in
                     (match uu____7393 with
                      | (v11,decls1) ->
                          let uu____7404 = encode_term v2 env in
                          (match uu____7404 with
                           | (v21,decls2) ->
                               let uu____7415 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7415,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7419)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7445)::(arg,uu____7447)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7482) ->
                     let e0 =
                       let uu____7500 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7500 in
                     ((let uu____7508 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7508
                       then
                         let uu____7509 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7509
                       else ());
                      (let e =
                         let uu____7514 =
                           let uu____7515 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7516 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7515
                             uu____7516 in
                         uu____7514 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7525),(arg,uu____7527)::[]) -> encode_term arg env
                 | uu____7552 ->
                     let uu____7565 = encode_args args_e env in
                     (match uu____7565 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7620 = encode_term head1 env in
                            match uu____7620 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7684 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7684 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7762  ->
                                                 fun uu____7763  ->
                                                   match (uu____7762,
                                                           uu____7763)
                                                   with
                                                   | ((bv,uu____7785),
                                                      (a,uu____7787)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7805 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7805
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7810 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7810 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7825 =
                                                   let uu____7832 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7841 =
                                                     let uu____7842 =
                                                       let uu____7843 =
                                                         let uu____7844 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7844 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7843 in
                                                     varops.mk_unique
                                                       uu____7842 in
                                                   (uu____7832,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7841) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7825 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7861 = lookup_free_var_sym env fv in
                            match uu____7861 with
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
                                   FStar_Syntax_Syntax.pos = uu____7892;
                                   FStar_Syntax_Syntax.vars = uu____7893;_},uu____7894)
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
                                   FStar_Syntax_Syntax.pos = uu____7905;
                                   FStar_Syntax_Syntax.vars = uu____7906;_},uu____7907)
                                ->
                                let uu____7912 =
                                  let uu____7913 =
                                    let uu____7918 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7918
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7913
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7912
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7948 =
                                  let uu____7949 =
                                    let uu____7954 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7954
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7949
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7948
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7983,(FStar_Util.Inl t1,uu____7985),uu____7986)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8035,(FStar_Util.Inr c,uu____8037),uu____8038)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8087 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8114 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8114 in
                               let uu____8115 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8115 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8131;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8132;_},uu____8133)
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
                                     | uu____8147 ->
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
           let uu____8196 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8196 with
            | (bs1,body1,opening) ->
                let fallback uu____8219 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8226 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8226, [decl]) in
                let is_impure rc =
                  let uu____8233 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8233 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8243 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8243
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8263 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8263
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8267 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8267)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8274 =
                         let uu____8275 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8275 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8274);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8277 =
                       (is_impure rc) &&
                         (let uu____8279 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8279) in
                     if uu____8277
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8286 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8286 with
                        | (vars,guards,envbody,decls,uu____8311) ->
                            let body2 =
                              let uu____8325 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8325
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8327 = encode_term body2 envbody in
                            (match uu____8327 with
                             | (body3,decls') ->
                                 let uu____8338 =
                                   let uu____8347 = codomain_eff rc in
                                   match uu____8347 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8366 = encode_term tfun env in
                                       (match uu____8366 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8338 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8398 =
                                          let uu____8409 =
                                            let uu____8410 =
                                              let uu____8415 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8415, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8410 in
                                          ([], vars, uu____8409) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8398 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8427 =
                                              let uu____8430 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8430
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8427 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8449 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8449 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8457 =
                                             let uu____8458 =
                                               let uu____8465 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8465) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8458 in
                                           (uu____8457,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8476 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8476 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8487 =
                                                    let uu____8488 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8488 = cache_size in
                                                  if uu____8487
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
                                                    let uu____8504 =
                                                      let uu____8505 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8505 in
                                                    varops.mk_unique
                                                      uu____8504 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8512 =
                                                    let uu____8519 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8519) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8512 in
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
                                                      let uu____8537 =
                                                        let uu____8538 =
                                                          let uu____8545 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8545,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8538 in
                                                      [uu____8537] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8558 =
                                                    let uu____8565 =
                                                      let uu____8566 =
                                                        let uu____8577 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8577) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8566 in
                                                    (uu____8565,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8558 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8594 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8594);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8597,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8598;
                          FStar_Syntax_Syntax.lbunivs = uu____8599;
                          FStar_Syntax_Syntax.lbtyp = uu____8600;
                          FStar_Syntax_Syntax.lbeff = uu____8601;
                          FStar_Syntax_Syntax.lbdef = uu____8602;_}::uu____8603),uu____8604)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8630;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8632;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8653 ->
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
              let uu____8723 = encode_term e1 env in
              match uu____8723 with
              | (ee1,decls1) ->
                  let uu____8734 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8734 with
                   | (xs,e21) ->
                       let uu____8759 = FStar_List.hd xs in
                       (match uu____8759 with
                        | (x1,uu____8773) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8775 = encode_body e21 env' in
                            (match uu____8775 with
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
            let uu____8807 =
              let uu____8814 =
                let uu____8815 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8815 in
              gen_term_var env uu____8814 in
            match uu____8807 with
            | (scrsym,scr',env1) ->
                let uu____8823 = encode_term e env1 in
                (match uu____8823 with
                 | (scr,decls) ->
                     let uu____8834 =
                       let encode_branch b uu____8859 =
                         match uu____8859 with
                         | (else_case,decls1) ->
                             let uu____8878 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8878 with
                              | (p,w,br) ->
                                  let uu____8904 = encode_pat env1 p in
                                  (match uu____8904 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8941  ->
                                                   match uu____8941 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8948 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8970 =
                                               encode_term w1 env2 in
                                             (match uu____8970 with
                                              | (w2,decls2) ->
                                                  let uu____8983 =
                                                    let uu____8984 =
                                                      let uu____8989 =
                                                        let uu____8990 =
                                                          let uu____8995 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8995) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8990 in
                                                      (guard, uu____8989) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8984 in
                                                  (uu____8983, decls2)) in
                                       (match uu____8948 with
                                        | (guard1,decls2) ->
                                            let uu____9008 =
                                              encode_br br env2 in
                                            (match uu____9008 with
                                             | (br1,decls3) ->
                                                 let uu____9021 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9021,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8834 with
                      | (match_tm,decls1) ->
                          let uu____9040 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9040, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9080 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9080
       then
         let uu____9081 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9081
       else ());
      (let uu____9083 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9083 with
       | (vars,pat_term) ->
           let uu____9100 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9153  ->
                     fun v1  ->
                       match uu____9153 with
                       | (env1,vars1) ->
                           let uu____9205 = gen_term_var env1 v1 in
                           (match uu____9205 with
                            | (xx,uu____9227,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9100 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9306 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9307 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9308 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9316 = encode_const c env1 in
                      (match uu____9316 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9330::uu____9331 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9334 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9357 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9357 with
                        | (uu____9364,uu____9365::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9368 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9401  ->
                                  match uu____9401 with
                                  | (arg,uu____9409) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9415 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9415)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9442) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9473 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9496 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9540  ->
                                  match uu____9540 with
                                  | (arg,uu____9554) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9560 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9560)) in
                      FStar_All.pipe_right uu____9496 FStar_List.flatten in
                let pat_term1 uu____9588 = encode_term pat_term env1 in
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
      let uu____9598 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9636  ->
                fun uu____9637  ->
                  match (uu____9636, uu____9637) with
                  | ((tms,decls),(t,uu____9673)) ->
                      let uu____9694 = encode_term t env in
                      (match uu____9694 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9598 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9751 = FStar_Syntax_Util.list_elements e in
        match uu____9751 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9772 =
          let uu____9787 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9787 FStar_Syntax_Util.head_and_args in
        match uu____9772 with
        | (head1,args) ->
            let uu____9826 =
              let uu____9839 =
                let uu____9840 = FStar_Syntax_Util.un_uinst head1 in
                uu____9840.FStar_Syntax_Syntax.n in
              (uu____9839, args) in
            (match uu____9826 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9854,uu____9855)::(e,uu____9857)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9892 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9928 =
            let uu____9943 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9943 FStar_Syntax_Util.head_and_args in
          match uu____9928 with
          | (head1,args) ->
              let uu____9984 =
                let uu____9997 =
                  let uu____9998 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9998.FStar_Syntax_Syntax.n in
                (uu____9997, args) in
              (match uu____9984 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10015)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10042 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10064 = smt_pat_or1 t1 in
            (match uu____10064 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10080 = list_elements1 e in
                 FStar_All.pipe_right uu____10080
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10098 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10098
                           (FStar_List.map one_pat)))
             | uu____10109 ->
                 let uu____10114 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10114])
        | uu____10135 ->
            let uu____10138 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10138] in
      let uu____10159 =
        let uu____10178 =
          let uu____10179 = FStar_Syntax_Subst.compress t in
          uu____10179.FStar_Syntax_Syntax.n in
        match uu____10178 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10218 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10218 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10261;
                        FStar_Syntax_Syntax.effect_name = uu____10262;
                        FStar_Syntax_Syntax.result_typ = uu____10263;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10265)::(post,uu____10267)::(pats,uu____10269)::[];
                        FStar_Syntax_Syntax.flags = uu____10270;_}
                      ->
                      let uu____10311 = lemma_pats pats in
                      (binders1, pre, post, uu____10311)
                  | uu____10328 -> failwith "impos"))
        | uu____10347 -> failwith "Impos" in
      match uu____10159 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___342_10395 = env in
            {
              bindings = (uu___342_10395.bindings);
              depth = (uu___342_10395.depth);
              tcenv = (uu___342_10395.tcenv);
              warn = (uu___342_10395.warn);
              cache = (uu___342_10395.cache);
              nolabels = (uu___342_10395.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___342_10395.encode_non_total_function_typ);
              current_module_name = (uu___342_10395.current_module_name)
            } in
          let uu____10396 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10396 with
           | (vars,guards,env2,decls,uu____10421) ->
               let uu____10434 =
                 let uu____10449 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10503 =
                             let uu____10514 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2)) in
                             FStar_All.pipe_right uu____10514
                               FStar_List.unzip in
                           match uu____10503 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10449 FStar_List.unzip in
               (match uu____10434 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___343_10666 = env2 in
                      {
                        bindings = (uu___343_10666.bindings);
                        depth = (uu___343_10666.depth);
                        tcenv = (uu___343_10666.tcenv);
                        warn = (uu___343_10666.warn);
                        cache = (uu___343_10666.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___343_10666.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___343_10666.encode_non_total_function_typ);
                        current_module_name =
                          (uu___343_10666.current_module_name)
                      } in
                    let uu____10667 =
                      let uu____10672 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10672 env3 in
                    (match uu____10667 with
                     | (pre1,decls'') ->
                         let uu____10679 =
                           let uu____10684 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10684 env3 in
                         (match uu____10679 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10694 =
                                let uu____10695 =
                                  let uu____10706 =
                                    let uu____10707 =
                                      let uu____10712 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10712, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10707 in
                                  (pats, vars, uu____10706) in
                                FStar_SMTEncoding_Util.mkForall uu____10695 in
                              (uu____10694, decls1)))))
and encode_smt_pattern:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let uu____10725 = FStar_Syntax_Util.head_and_args t in
      match uu____10725 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1 in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10784::(x,uu____10786)::(t1,uu____10788)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10835 = encode_term x env in
               (match uu____10835 with
                | (x1,decls) ->
                    let uu____10848 = encode_term t1 env in
                    (match uu____10848 with
                     | (t2,decls') ->
                         let uu____10861 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                         (uu____10861, (FStar_List.append decls decls'))))
           | uu____10864 -> encode_term t env)
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10887 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10887
        then
          let uu____10888 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10889 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10888 uu____10889
        else () in
      let enc f r l =
        let uu____10922 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10950 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10950 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10922 with
        | (decls,args) ->
            let uu____10979 =
              let uu___344_10980 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___344_10980.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___344_10980.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10979, decls) in
      let const_op f r uu____11011 =
        let uu____11024 = f r in (uu____11024, []) in
      let un_op f l =
        let uu____11043 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11043 in
      let bin_op f uu___318_11059 =
        match uu___318_11059 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11070 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11104 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11127  ->
                 match uu____11127 with
                 | (t,uu____11141) ->
                     let uu____11142 = encode_formula t env in
                     (match uu____11142 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11104 with
        | (decls,phis) ->
            let uu____11171 =
              let uu___345_11172 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___345_11172.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___345_11172.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11171, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11233  ->
               match uu____11233 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11252) -> false
                    | uu____11253 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11268 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11268
        else
          (let uu____11282 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11282 r rf) in
      let mk_imp1 r uu___319_11307 =
        match uu___319_11307 with
        | (lhs,uu____11313)::(rhs,uu____11315)::[] ->
            let uu____11342 = encode_formula rhs env in
            (match uu____11342 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11357) ->
                      (l1, decls1)
                  | uu____11362 ->
                      let uu____11363 = encode_formula lhs env in
                      (match uu____11363 with
                       | (l2,decls2) ->
                           let uu____11374 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11374, (FStar_List.append decls1 decls2)))))
        | uu____11377 -> failwith "impossible" in
      let mk_ite r uu___320_11398 =
        match uu___320_11398 with
        | (guard,uu____11404)::(_then,uu____11406)::(_else,uu____11408)::[]
            ->
            let uu____11445 = encode_formula guard env in
            (match uu____11445 with
             | (g,decls1) ->
                 let uu____11456 = encode_formula _then env in
                 (match uu____11456 with
                  | (t,decls2) ->
                      let uu____11467 = encode_formula _else env in
                      (match uu____11467 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11481 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11506 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11506 in
      let connectives =
        let uu____11524 =
          let uu____11537 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11537) in
        let uu____11554 =
          let uu____11569 =
            let uu____11582 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11582) in
          let uu____11599 =
            let uu____11614 =
              let uu____11629 =
                let uu____11642 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11642) in
              let uu____11659 =
                let uu____11674 =
                  let uu____11689 =
                    let uu____11702 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11702) in
                  [uu____11689;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11674 in
              uu____11629 :: uu____11659 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11614 in
          uu____11569 :: uu____11599 in
        uu____11524 :: uu____11554 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12023 = encode_formula phi' env in
            (match uu____12023 with
             | (phi2,decls) ->
                 let uu____12034 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12034, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12035 ->
            let uu____12042 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12042 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12081 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12081 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12093;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12095;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12116 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12116 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12163::(x,uu____12165)::(t,uu____12167)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12214 = encode_term x env in
                 (match uu____12214 with
                  | (x1,decls) ->
                      let uu____12225 = encode_term t env in
                      (match uu____12225 with
                       | (t1,decls') ->
                           let uu____12236 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12236, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12241)::(msg,uu____12243)::(phi2,uu____12245)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12290 =
                   let uu____12295 =
                     let uu____12296 = FStar_Syntax_Subst.compress r in
                     uu____12296.FStar_Syntax_Syntax.n in
                   let uu____12299 =
                     let uu____12300 = FStar_Syntax_Subst.compress msg in
                     uu____12300.FStar_Syntax_Syntax.n in
                   (uu____12295, uu____12299) in
                 (match uu____12290 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12309))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12315 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12322)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12347 when head_redex env head2 ->
                 let uu____12360 = whnf env phi1 in
                 encode_formula uu____12360 env
             | uu____12361 ->
                 let uu____12374 = encode_term phi1 env in
                 (match uu____12374 with
                  | (tt,decls) ->
                      let uu____12385 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___346_12388 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___346_12388.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___346_12388.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12385, decls)))
        | uu____12389 ->
            let uu____12390 = encode_term phi1 env in
            (match uu____12390 with
             | (tt,decls) ->
                 let uu____12401 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___347_12404 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___347_12404.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___347_12404.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12401, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12440 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12440 with
        | (vars,guards,env2,decls,uu____12479) ->
            let uu____12492 =
              let uu____12505 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12557 =
                          let uu____12568 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12608  ->
                                    match uu____12608 with
                                    | (t,uu____12622) ->
                                        encode_smt_pattern t
                                          (let uu___348_12628 = env2 in
                                           {
                                             bindings =
                                               (uu___348_12628.bindings);
                                             depth = (uu___348_12628.depth);
                                             tcenv = (uu___348_12628.tcenv);
                                             warn = (uu___348_12628.warn);
                                             cache = (uu___348_12628.cache);
                                             nolabels =
                                               (uu___348_12628.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___348_12628.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___348_12628.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12568 FStar_List.unzip in
                        match uu____12557 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12505 FStar_List.unzip in
            (match uu____12492 with
             | (pats,decls') ->
                 let uu____12737 = encode_formula body env2 in
                 (match uu____12737 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12769;
                             FStar_SMTEncoding_Term.rng = uu____12770;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12785 -> guards in
                      let uu____12790 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12790, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12850  ->
                   match uu____12850 with
                   | (x,uu____12856) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12864 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12876 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12876) uu____12864 tl1 in
             let uu____12879 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12906  ->
                       match uu____12906 with
                       | (b,uu____12912) ->
                           let uu____12913 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12913)) in
             (match uu____12879 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12919) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12933 =
                    let uu____12934 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12934 in
                  FStar_Errors.warn pos uu____12933) in
       let uu____12935 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12935 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12944 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13002  ->
                     match uu____13002 with
                     | (l,uu____13016) -> FStar_Ident.lid_equals op l)) in
           (match uu____12944 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13049,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13089 = encode_q_body env vars pats body in
             match uu____13089 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13134 =
                     let uu____13145 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13145) in
                   FStar_SMTEncoding_Term.mkForall uu____13134
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13164 = encode_q_body env vars pats body in
             match uu____13164 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13208 =
                   let uu____13209 =
                     let uu____13220 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13220) in
                   FStar_SMTEncoding_Term.mkExists uu____13209
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13208, decls))))
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
  let uu____13313 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13313 with
  | (asym,a) ->
      let uu____13320 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13320 with
       | (xsym,x) ->
           let uu____13327 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13327 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13371 =
                      let uu____13382 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13382, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13371 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13408 =
                      let uu____13415 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13415) in
                    FStar_SMTEncoding_Util.mkApp uu____13408 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13428 =
                    let uu____13431 =
                      let uu____13434 =
                        let uu____13437 =
                          let uu____13438 =
                            let uu____13445 =
                              let uu____13446 =
                                let uu____13457 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13457) in
                              FStar_SMTEncoding_Util.mkForall uu____13446 in
                            (uu____13445, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13438 in
                        let uu____13474 =
                          let uu____13477 =
                            let uu____13478 =
                              let uu____13485 =
                                let uu____13486 =
                                  let uu____13497 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13497) in
                                FStar_SMTEncoding_Util.mkForall uu____13486 in
                              (uu____13485,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13478 in
                          [uu____13477] in
                        uu____13437 :: uu____13474 in
                      xtok_decl :: uu____13434 in
                    xname_decl :: uu____13431 in
                  (xtok1, uu____13428) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13588 =
                    let uu____13601 =
                      let uu____13610 =
                        let uu____13611 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13611 in
                      quant axy uu____13610 in
                    (FStar_Parser_Const.op_Eq, uu____13601) in
                  let uu____13620 =
                    let uu____13635 =
                      let uu____13648 =
                        let uu____13657 =
                          let uu____13658 =
                            let uu____13659 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13659 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13658 in
                        quant axy uu____13657 in
                      (FStar_Parser_Const.op_notEq, uu____13648) in
                    let uu____13668 =
                      let uu____13683 =
                        let uu____13696 =
                          let uu____13705 =
                            let uu____13706 =
                              let uu____13707 =
                                let uu____13712 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13713 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13712, uu____13713) in
                              FStar_SMTEncoding_Util.mkLT uu____13707 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13706 in
                          quant xy uu____13705 in
                        (FStar_Parser_Const.op_LT, uu____13696) in
                      let uu____13722 =
                        let uu____13737 =
                          let uu____13750 =
                            let uu____13759 =
                              let uu____13760 =
                                let uu____13761 =
                                  let uu____13766 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13767 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13766, uu____13767) in
                                FStar_SMTEncoding_Util.mkLTE uu____13761 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13760 in
                            quant xy uu____13759 in
                          (FStar_Parser_Const.op_LTE, uu____13750) in
                        let uu____13776 =
                          let uu____13791 =
                            let uu____13804 =
                              let uu____13813 =
                                let uu____13814 =
                                  let uu____13815 =
                                    let uu____13820 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13821 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13820, uu____13821) in
                                  FStar_SMTEncoding_Util.mkGT uu____13815 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13814 in
                              quant xy uu____13813 in
                            (FStar_Parser_Const.op_GT, uu____13804) in
                          let uu____13830 =
                            let uu____13845 =
                              let uu____13858 =
                                let uu____13867 =
                                  let uu____13868 =
                                    let uu____13869 =
                                      let uu____13874 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13875 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13874, uu____13875) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13869 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13868 in
                                quant xy uu____13867 in
                              (FStar_Parser_Const.op_GTE, uu____13858) in
                            let uu____13884 =
                              let uu____13899 =
                                let uu____13912 =
                                  let uu____13921 =
                                    let uu____13922 =
                                      let uu____13923 =
                                        let uu____13928 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13929 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13928, uu____13929) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13923 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13922 in
                                  quant xy uu____13921 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13912) in
                              let uu____13938 =
                                let uu____13953 =
                                  let uu____13966 =
                                    let uu____13975 =
                                      let uu____13976 =
                                        let uu____13977 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13977 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13976 in
                                    quant qx uu____13975 in
                                  (FStar_Parser_Const.op_Minus, uu____13966) in
                                let uu____13986 =
                                  let uu____14001 =
                                    let uu____14014 =
                                      let uu____14023 =
                                        let uu____14024 =
                                          let uu____14025 =
                                            let uu____14030 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14031 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14030, uu____14031) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14025 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14024 in
                                      quant xy uu____14023 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14014) in
                                  let uu____14040 =
                                    let uu____14055 =
                                      let uu____14068 =
                                        let uu____14077 =
                                          let uu____14078 =
                                            let uu____14079 =
                                              let uu____14084 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14085 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14084, uu____14085) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14079 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14078 in
                                        quant xy uu____14077 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14068) in
                                    let uu____14094 =
                                      let uu____14109 =
                                        let uu____14122 =
                                          let uu____14131 =
                                            let uu____14132 =
                                              let uu____14133 =
                                                let uu____14138 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14139 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14138, uu____14139) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14133 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14132 in
                                          quant xy uu____14131 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14122) in
                                      let uu____14148 =
                                        let uu____14163 =
                                          let uu____14176 =
                                            let uu____14185 =
                                              let uu____14186 =
                                                let uu____14187 =
                                                  let uu____14192 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14193 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14192, uu____14193) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14187 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14186 in
                                            quant xy uu____14185 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14176) in
                                        let uu____14202 =
                                          let uu____14217 =
                                            let uu____14230 =
                                              let uu____14239 =
                                                let uu____14240 =
                                                  let uu____14241 =
                                                    let uu____14246 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14247 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14246,
                                                      uu____14247) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14241 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14240 in
                                              quant xy uu____14239 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14230) in
                                          let uu____14256 =
                                            let uu____14271 =
                                              let uu____14284 =
                                                let uu____14293 =
                                                  let uu____14294 =
                                                    let uu____14295 =
                                                      let uu____14300 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14301 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14300,
                                                        uu____14301) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14295 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14294 in
                                                quant xy uu____14293 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14284) in
                                            let uu____14310 =
                                              let uu____14325 =
                                                let uu____14338 =
                                                  let uu____14347 =
                                                    let uu____14348 =
                                                      let uu____14349 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14349 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14348 in
                                                  quant qx uu____14347 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14338) in
                                              [uu____14325] in
                                            uu____14271 :: uu____14310 in
                                          uu____14217 :: uu____14256 in
                                        uu____14163 :: uu____14202 in
                                      uu____14109 :: uu____14148 in
                                    uu____14055 :: uu____14094 in
                                  uu____14001 :: uu____14040 in
                                uu____13953 :: uu____13986 in
                              uu____13899 :: uu____13938 in
                            uu____13845 :: uu____13884 in
                          uu____13791 :: uu____13830 in
                        uu____13737 :: uu____13776 in
                      uu____13683 :: uu____13722 in
                    uu____13635 :: uu____13668 in
                  uu____13588 :: uu____13620 in
                let mk1 l v1 =
                  let uu____14563 =
                    let uu____14572 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14630  ->
                              match uu____14630 with
                              | (l',uu____14644) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14572
                      (FStar_Option.map
                         (fun uu____14704  ->
                            match uu____14704 with | (uu____14723,b) -> b v1)) in
                  FStar_All.pipe_right uu____14563 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14794  ->
                          match uu____14794 with
                          | (l',uu____14808) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14846 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14846 with
        | (xxsym,xx) ->
            let uu____14853 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14853 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14863 =
                   let uu____14870 =
                     let uu____14871 =
                       let uu____14882 =
                         let uu____14883 =
                           let uu____14888 =
                             let uu____14889 =
                               let uu____14894 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14894) in
                             FStar_SMTEncoding_Util.mkEq uu____14889 in
                           (xx_has_type, uu____14888) in
                         FStar_SMTEncoding_Util.mkImp uu____14883 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14882) in
                     FStar_SMTEncoding_Util.mkForall uu____14871 in
                   let uu____14919 =
                     let uu____14920 =
                       let uu____14921 =
                         let uu____14922 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14922 in
                       Prims.strcat module_name uu____14921 in
                     varops.mk_unique uu____14920 in
                   (uu____14870, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14919) in
                 FStar_SMTEncoding_Util.mkAssume uu____14863)
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
    let uu____14958 =
      let uu____14959 =
        let uu____14966 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14966, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14959 in
    let uu____14969 =
      let uu____14972 =
        let uu____14973 =
          let uu____14980 =
            let uu____14981 =
              let uu____14992 =
                let uu____14993 =
                  let uu____14998 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14998) in
                FStar_SMTEncoding_Util.mkImp uu____14993 in
              ([[typing_pred]], [xx], uu____14992) in
            mkForall_fuel uu____14981 in
          (uu____14980, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14973 in
      [uu____14972] in
    uu____14958 :: uu____14969 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15040 =
      let uu____15041 =
        let uu____15048 =
          let uu____15049 =
            let uu____15060 =
              let uu____15065 =
                let uu____15068 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15068] in
              [uu____15065] in
            let uu____15073 =
              let uu____15074 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15074 tt in
            (uu____15060, [bb], uu____15073) in
          FStar_SMTEncoding_Util.mkForall uu____15049 in
        (uu____15048, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15041 in
    let uu____15095 =
      let uu____15098 =
        let uu____15099 =
          let uu____15106 =
            let uu____15107 =
              let uu____15118 =
                let uu____15119 =
                  let uu____15124 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15124) in
                FStar_SMTEncoding_Util.mkImp uu____15119 in
              ([[typing_pred]], [xx], uu____15118) in
            mkForall_fuel uu____15107 in
          (uu____15106, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15099 in
      [uu____15098] in
    uu____15040 :: uu____15095 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15174 =
        let uu____15175 =
          let uu____15182 =
            let uu____15185 =
              let uu____15188 =
                let uu____15191 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15192 =
                  let uu____15195 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15195] in
                uu____15191 :: uu____15192 in
              tt :: uu____15188 in
            tt :: uu____15185 in
          ("Prims.Precedes", uu____15182) in
        FStar_SMTEncoding_Util.mkApp uu____15175 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15174 in
    let precedes_y_x =
      let uu____15199 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15199 in
    let uu____15202 =
      let uu____15203 =
        let uu____15210 =
          let uu____15211 =
            let uu____15222 =
              let uu____15227 =
                let uu____15230 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15230] in
              [uu____15227] in
            let uu____15235 =
              let uu____15236 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15236 tt in
            (uu____15222, [bb], uu____15235) in
          FStar_SMTEncoding_Util.mkForall uu____15211 in
        (uu____15210, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15203 in
    let uu____15257 =
      let uu____15260 =
        let uu____15261 =
          let uu____15268 =
            let uu____15269 =
              let uu____15280 =
                let uu____15281 =
                  let uu____15286 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15286) in
                FStar_SMTEncoding_Util.mkImp uu____15281 in
              ([[typing_pred]], [xx], uu____15280) in
            mkForall_fuel uu____15269 in
          (uu____15268, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15261 in
      let uu____15311 =
        let uu____15314 =
          let uu____15315 =
            let uu____15322 =
              let uu____15323 =
                let uu____15334 =
                  let uu____15335 =
                    let uu____15340 =
                      let uu____15341 =
                        let uu____15344 =
                          let uu____15347 =
                            let uu____15350 =
                              let uu____15351 =
                                let uu____15356 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15357 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15356, uu____15357) in
                              FStar_SMTEncoding_Util.mkGT uu____15351 in
                            let uu____15358 =
                              let uu____15361 =
                                let uu____15362 =
                                  let uu____15367 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15368 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15367, uu____15368) in
                                FStar_SMTEncoding_Util.mkGTE uu____15362 in
                              let uu____15369 =
                                let uu____15372 =
                                  let uu____15373 =
                                    let uu____15378 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15379 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15378, uu____15379) in
                                  FStar_SMTEncoding_Util.mkLT uu____15373 in
                                [uu____15372] in
                              uu____15361 :: uu____15369 in
                            uu____15350 :: uu____15358 in
                          typing_pred_y :: uu____15347 in
                        typing_pred :: uu____15344 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15341 in
                    (uu____15340, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15335 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15334) in
              mkForall_fuel uu____15323 in
            (uu____15322,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15315 in
        [uu____15314] in
      uu____15260 :: uu____15311 in
    uu____15202 :: uu____15257 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15425 =
      let uu____15426 =
        let uu____15433 =
          let uu____15434 =
            let uu____15445 =
              let uu____15450 =
                let uu____15453 = FStar_SMTEncoding_Term.boxString b in
                [uu____15453] in
              [uu____15450] in
            let uu____15458 =
              let uu____15459 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15459 tt in
            (uu____15445, [bb], uu____15458) in
          FStar_SMTEncoding_Util.mkForall uu____15434 in
        (uu____15433, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15426 in
    let uu____15480 =
      let uu____15483 =
        let uu____15484 =
          let uu____15491 =
            let uu____15492 =
              let uu____15503 =
                let uu____15504 =
                  let uu____15509 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15509) in
                FStar_SMTEncoding_Util.mkImp uu____15504 in
              ([[typing_pred]], [xx], uu____15503) in
            mkForall_fuel uu____15492 in
          (uu____15491, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15484 in
      [uu____15483] in
    uu____15425 :: uu____15480 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15562 =
      let uu____15563 =
        let uu____15570 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15570, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15563 in
    [uu____15562] in
  let mk_and_interp env conj uu____15582 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15607 =
      let uu____15608 =
        let uu____15615 =
          let uu____15616 =
            let uu____15627 =
              let uu____15628 =
                let uu____15633 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15633, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15628 in
            ([[l_and_a_b]], [aa; bb], uu____15627) in
          FStar_SMTEncoding_Util.mkForall uu____15616 in
        (uu____15615, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15608 in
    [uu____15607] in
  let mk_or_interp env disj uu____15671 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15696 =
      let uu____15697 =
        let uu____15704 =
          let uu____15705 =
            let uu____15716 =
              let uu____15717 =
                let uu____15722 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15722, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15717 in
            ([[l_or_a_b]], [aa; bb], uu____15716) in
          FStar_SMTEncoding_Util.mkForall uu____15705 in
        (uu____15704, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15697 in
    [uu____15696] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15785 =
      let uu____15786 =
        let uu____15793 =
          let uu____15794 =
            let uu____15805 =
              let uu____15806 =
                let uu____15811 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15811, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15806 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15805) in
          FStar_SMTEncoding_Util.mkForall uu____15794 in
        (uu____15793, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15786 in
    [uu____15785] in
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
    let uu____15884 =
      let uu____15885 =
        let uu____15892 =
          let uu____15893 =
            let uu____15904 =
              let uu____15905 =
                let uu____15910 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15910, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15905 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15904) in
          FStar_SMTEncoding_Util.mkForall uu____15893 in
        (uu____15892, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15885 in
    [uu____15884] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15981 =
      let uu____15982 =
        let uu____15989 =
          let uu____15990 =
            let uu____16001 =
              let uu____16002 =
                let uu____16007 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16007, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16002 in
            ([[l_imp_a_b]], [aa; bb], uu____16001) in
          FStar_SMTEncoding_Util.mkForall uu____15990 in
        (uu____15989, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15982 in
    [uu____15981] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16070 =
      let uu____16071 =
        let uu____16078 =
          let uu____16079 =
            let uu____16090 =
              let uu____16091 =
                let uu____16096 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16096, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16091 in
            ([[l_iff_a_b]], [aa; bb], uu____16090) in
          FStar_SMTEncoding_Util.mkForall uu____16079 in
        (uu____16078, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16071 in
    [uu____16070] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16148 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16148 in
    let uu____16151 =
      let uu____16152 =
        let uu____16159 =
          let uu____16160 =
            let uu____16171 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16171) in
          FStar_SMTEncoding_Util.mkForall uu____16160 in
        (uu____16159, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16152 in
    [uu____16151] in
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
      let uu____16231 =
        let uu____16238 =
          let uu____16241 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16241] in
        ("Valid", uu____16238) in
      FStar_SMTEncoding_Util.mkApp uu____16231 in
    let uu____16244 =
      let uu____16245 =
        let uu____16252 =
          let uu____16253 =
            let uu____16264 =
              let uu____16265 =
                let uu____16270 =
                  let uu____16271 =
                    let uu____16282 =
                      let uu____16287 =
                        let uu____16290 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16290] in
                      [uu____16287] in
                    let uu____16295 =
                      let uu____16296 =
                        let uu____16301 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16301, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16296 in
                    (uu____16282, [xx1], uu____16295) in
                  FStar_SMTEncoding_Util.mkForall uu____16271 in
                (uu____16270, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16265 in
            ([[l_forall_a_b]], [aa; bb], uu____16264) in
          FStar_SMTEncoding_Util.mkForall uu____16253 in
        (uu____16252, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16245 in
    [uu____16244] in
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
      let uu____16383 =
        let uu____16390 =
          let uu____16393 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16393] in
        ("Valid", uu____16390) in
      FStar_SMTEncoding_Util.mkApp uu____16383 in
    let uu____16396 =
      let uu____16397 =
        let uu____16404 =
          let uu____16405 =
            let uu____16416 =
              let uu____16417 =
                let uu____16422 =
                  let uu____16423 =
                    let uu____16434 =
                      let uu____16439 =
                        let uu____16442 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16442] in
                      [uu____16439] in
                    let uu____16447 =
                      let uu____16448 =
                        let uu____16453 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16453, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16448 in
                    (uu____16434, [xx1], uu____16447) in
                  FStar_SMTEncoding_Util.mkExists uu____16423 in
                (uu____16422, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16417 in
            ([[l_exists_a_b]], [aa; bb], uu____16416) in
          FStar_SMTEncoding_Util.mkForall uu____16405 in
        (uu____16404, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16397 in
    [uu____16396] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16513 =
      let uu____16514 =
        let uu____16521 =
          let uu____16522 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16522 range_ty in
        let uu____16523 = varops.mk_unique "typing_range_const" in
        (uu____16521, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16523) in
      FStar_SMTEncoding_Util.mkAssume uu____16514 in
    [uu____16513] in
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
        let uu____16557 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16557 x1 t in
      let uu____16558 =
        let uu____16569 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16569) in
      FStar_SMTEncoding_Util.mkForall uu____16558 in
    let uu____16592 =
      let uu____16593 =
        let uu____16600 =
          let uu____16601 =
            let uu____16612 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16612) in
          FStar_SMTEncoding_Util.mkForall uu____16601 in
        (uu____16600,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16593 in
    [uu____16592] in
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
          let uu____16936 =
            FStar_Util.find_opt
              (fun uu____16962  ->
                 match uu____16962 with
                 | (l,uu____16974) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16936 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16999,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17035 = encode_function_type_as_formula t env in
        match uu____17035 with
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
              let uu____17075 =
                ((let uu____17078 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17078) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17075
              then
                let uu____17085 = new_term_constant_and_tok_from_lid env lid in
                match uu____17085 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17104 =
                        let uu____17105 = FStar_Syntax_Subst.compress t_norm in
                        uu____17105.FStar_Syntax_Syntax.n in
                      match uu____17104 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17111) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17141  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17146 -> [] in
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
                (let uu____17160 = prims.is lid in
                 if uu____17160
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17168 = prims.mk lid vname in
                   match uu____17168 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17192 =
                      let uu____17203 = curried_arrow_formals_comp t_norm in
                      match uu____17203 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17221 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17221
                            then
                              let uu____17222 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___349_17225 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___349_17225.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___349_17225.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___349_17225.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___349_17225.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___349_17225.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___349_17225.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___349_17225.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___349_17225.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___349_17225.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___349_17225.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___349_17225.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___349_17225.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___349_17225.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___349_17225.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___349_17225.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___349_17225.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___349_17225.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___349_17225.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___349_17225.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___349_17225.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___349_17225.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___349_17225.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___349_17225.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___349_17225.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___349_17225.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___349_17225.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___349_17225.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___349_17225.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___349_17225.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___349_17225.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___349_17225.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___349_17225.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___349_17225.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17222
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17237 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17237)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17192 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17282 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17282 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17303 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___321_17345  ->
                                       match uu___321_17345 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17349 =
                                             FStar_Util.prefix vars in
                                           (match uu____17349 with
                                            | (uu____17370,(xxsym,uu____17372))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17390 =
                                                  let uu____17391 =
                                                    let uu____17398 =
                                                      let uu____17399 =
                                                        let uu____17410 =
                                                          let uu____17411 =
                                                            let uu____17416 =
                                                              let uu____17417
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17417 in
                                                            (vapp,
                                                              uu____17416) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17411 in
                                                        ([[vapp]], vars,
                                                          uu____17410) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17399 in
                                                    (uu____17398,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17391 in
                                                [uu____17390])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17436 =
                                             FStar_Util.prefix vars in
                                           (match uu____17436 with
                                            | (uu____17457,(xxsym,uu____17459))
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
                                                let uu____17482 =
                                                  let uu____17483 =
                                                    let uu____17490 =
                                                      let uu____17491 =
                                                        let uu____17502 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17502) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17491 in
                                                    (uu____17490,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17483 in
                                                [uu____17482])
                                       | uu____17519 -> [])) in
                             let uu____17520 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17520 with
                              | (vars,guards,env',decls1,uu____17547) ->
                                  let uu____17560 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17569 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17569, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17571 =
                                          encode_formula p env' in
                                        (match uu____17571 with
                                         | (g,ds) ->
                                             let uu____17582 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17582,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17560 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17595 =
                                           let uu____17602 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17602) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17595 in
                                       let uu____17611 =
                                         let vname_decl =
                                           let uu____17619 =
                                             let uu____17630 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17640  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17630,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17619 in
                                         let uu____17649 =
                                           let env2 =
                                             let uu___350_17655 = env1 in
                                             {
                                               bindings =
                                                 (uu___350_17655.bindings);
                                               depth = (uu___350_17655.depth);
                                               tcenv = (uu___350_17655.tcenv);
                                               warn = (uu___350_17655.warn);
                                               cache = (uu___350_17655.cache);
                                               nolabels =
                                                 (uu___350_17655.nolabels);
                                               use_zfuel_name =
                                                 (uu___350_17655.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___350_17655.current_module_name)
                                             } in
                                           let uu____17656 =
                                             let uu____17657 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17657 in
                                           if uu____17656
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17649 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17672::uu____17673 ->
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
                                                     let uu____17713 =
                                                       let uu____17724 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17724) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17713 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17751 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17754 =
                                               match formals with
                                               | [] ->
                                                   let uu____17771 =
                                                     let uu____17772 =
                                                       let uu____17775 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17775 in
                                                     push_free_var env1 lid
                                                       vname uu____17772 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17771)
                                               | uu____17780 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17787 =
                                                       let uu____17794 =
                                                         let uu____17795 =
                                                           let uu____17806 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17806) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17795 in
                                                       (uu____17794,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17787 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17754 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17611 with
                                        | (decls2,env2) ->
                                            let uu____17849 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17857 =
                                                encode_term res_t1 env' in
                                              match uu____17857 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17870 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17870, decls) in
                                            (match uu____17849 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17881 =
                                                     let uu____17888 =
                                                       let uu____17889 =
                                                         let uu____17900 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17900) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17889 in
                                                     (uu____17888,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17881 in
                                                 let freshness =
                                                   let uu____17916 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17916
                                                   then
                                                     let uu____17921 =
                                                       let uu____17922 =
                                                         let uu____17933 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17944 =
                                                           varops.next_id () in
                                                         (vname, uu____17933,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17944) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17922 in
                                                     let uu____17947 =
                                                       let uu____17950 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17950] in
                                                     uu____17921 ::
                                                       uu____17947
                                                   else [] in
                                                 let g =
                                                   let uu____17955 =
                                                     let uu____17958 =
                                                       let uu____17961 =
                                                         let uu____17964 =
                                                           let uu____17967 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17967 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17964 in
                                                       FStar_List.append
                                                         decls3 uu____17961 in
                                                     FStar_List.append decls2
                                                       uu____17958 in
                                                   FStar_List.append decls11
                                                     uu____17955 in
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
          let uu____17998 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17998 with
          | FStar_Pervasives_Native.None  ->
              let uu____18035 = encode_free_var false env x t t_norm [] in
              (match uu____18035 with
               | (decls,env1) ->
                   let uu____18062 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18062 with
                    | (n1,x',uu____18089) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18110) ->
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
            let uu____18165 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18165 with
            | (decls,env1) ->
                let uu____18184 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18184
                then
                  let uu____18191 =
                    let uu____18194 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18194 in
                  (uu____18191, env1)
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
             (fun uu____18246  ->
                fun lb  ->
                  match uu____18246 with
                  | (decls,env1) ->
                      let uu____18266 =
                        let uu____18273 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18273
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18266 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18294 = FStar_Syntax_Util.head_and_args t in
    match uu____18294 with
    | (hd1,args) ->
        let uu____18331 =
          let uu____18332 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18332.FStar_Syntax_Syntax.n in
        (match uu____18331 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18336,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18355 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18377  ->
      fun quals  ->
        match uu____18377 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18453 = FStar_Util.first_N nbinders formals in
              match uu____18453 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18534  ->
                         fun uu____18535  ->
                           match (uu____18534, uu____18535) with
                           | ((formal,uu____18553),(binder,uu____18555)) ->
                               let uu____18564 =
                                 let uu____18571 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18571) in
                               FStar_Syntax_Syntax.NT uu____18564) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18579 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18610  ->
                              match uu____18610 with
                              | (x,i) ->
                                  let uu____18621 =
                                    let uu___351_18622 = x in
                                    let uu____18623 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___351_18622.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___351_18622.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18623
                                    } in
                                  (uu____18621, i))) in
                    FStar_All.pipe_right uu____18579
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18641 =
                      let uu____18642 = FStar_Syntax_Subst.compress body in
                      let uu____18643 =
                        let uu____18644 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18644 in
                      FStar_Syntax_Syntax.extend_app_n uu____18642
                        uu____18643 in
                    uu____18641 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18705 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18705
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___352_18708 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___352_18708.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___352_18708.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___352_18708.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___352_18708.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___352_18708.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___352_18708.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___352_18708.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___352_18708.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___352_18708.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___352_18708.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___352_18708.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___352_18708.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___352_18708.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___352_18708.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___352_18708.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___352_18708.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___352_18708.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___352_18708.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___352_18708.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___352_18708.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___352_18708.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___352_18708.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___352_18708.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___352_18708.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___352_18708.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___352_18708.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___352_18708.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___352_18708.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___352_18708.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___352_18708.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___352_18708.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___352_18708.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___352_18708.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18741 = FStar_Syntax_Util.abs_formals e in
                match uu____18741 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18805::uu____18806 ->
                         let uu____18821 =
                           let uu____18822 =
                             let uu____18825 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18825 in
                           uu____18822.FStar_Syntax_Syntax.n in
                         (match uu____18821 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18868 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18868 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18910 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18910
                                   then
                                     let uu____18945 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18945 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19039  ->
                                                   fun uu____19040  ->
                                                     match (uu____19039,
                                                             uu____19040)
                                                     with
                                                     | ((x,uu____19058),
                                                        (b,uu____19060)) ->
                                                         let uu____19069 =
                                                           let uu____19076 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19076) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19069)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19078 =
                                            let uu____19099 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19099) in
                                          (uu____19078, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19167 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19167 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19256) ->
                              let uu____19261 =
                                let uu____19282 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19282 in
                              (uu____19261, true)
                          | uu____19347 when Prims.op_Negation norm1 ->
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
                          | uu____19349 ->
                              let uu____19350 =
                                let uu____19351 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19352 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19351
                                  uu____19352 in
                              failwith uu____19350)
                     | uu____19377 ->
                         let rec aux' t_norm2 =
                           let uu____19402 =
                             let uu____19403 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19403.FStar_Syntax_Syntax.n in
                           match uu____19402 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19444 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19444 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19472 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19472 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19552)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19557 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19613 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19613
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19625 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19719  ->
                            fun lb  ->
                              match uu____19719 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19814 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19814
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19817 =
                                      let uu____19832 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19832
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19817 with
                                    | (tok,decl,env2) ->
                                        let uu____19878 =
                                          let uu____19891 =
                                            let uu____19902 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19902, tok) in
                                          uu____19891 :: toks in
                                        (uu____19878, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19625 with
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
                        | uu____20085 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20093 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20093 vars)
                            else
                              (let uu____20095 =
                                 let uu____20102 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20102) in
                               FStar_SMTEncoding_Util.mkApp uu____20095) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20184;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20186;
                             FStar_Syntax_Syntax.lbeff = uu____20187;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20250 =
                              let uu____20257 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20257 with
                              | (tcenv',uu____20275,e_t) ->
                                  let uu____20281 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20292 -> failwith "Impossible" in
                                  (match uu____20281 with
                                   | (e1,t_norm1) ->
                                       ((let uu___355_20308 = env2 in
                                         {
                                           bindings =
                                             (uu___355_20308.bindings);
                                           depth = (uu___355_20308.depth);
                                           tcenv = tcenv';
                                           warn = (uu___355_20308.warn);
                                           cache = (uu___355_20308.cache);
                                           nolabels =
                                             (uu___355_20308.nolabels);
                                           use_zfuel_name =
                                             (uu___355_20308.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___355_20308.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___355_20308.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20250 with
                             | (env',e1,t_norm1) ->
                                 let uu____20318 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20318 with
                                  | ((binders,body,uu____20339,uu____20340),curry)
                                      ->
                                      ((let uu____20351 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20351
                                        then
                                          let uu____20352 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20353 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20352 uu____20353
                                        else ());
                                       (let uu____20355 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20355 with
                                        | (vars,guards,env'1,binder_decls,uu____20382)
                                            ->
                                            let body1 =
                                              let uu____20396 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20396
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20399 =
                                              let uu____20408 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20408
                                              then
                                                let uu____20419 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20420 =
                                                  encode_formula body1 env'1 in
                                                (uu____20419, uu____20420)
                                              else
                                                (let uu____20430 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20430)) in
                                            (match uu____20399 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20453 =
                                                     let uu____20460 =
                                                       let uu____20461 =
                                                         let uu____20472 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20472) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20461 in
                                                     let uu____20483 =
                                                       let uu____20486 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20486 in
                                                     (uu____20460,
                                                       uu____20483,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20453 in
                                                 let uu____20489 =
                                                   let uu____20492 =
                                                     let uu____20495 =
                                                       let uu____20498 =
                                                         let uu____20501 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20501 in
                                                       FStar_List.append
                                                         decls2 uu____20498 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20495 in
                                                   FStar_List.append decls1
                                                     uu____20492 in
                                                 (uu____20489, env2))))))
                        | uu____20506 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20591 = varops.fresh "fuel" in
                          (uu____20591, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20594 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20682  ->
                                  fun uu____20683  ->
                                    match (uu____20682, uu____20683) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20831 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20831 in
                                        let gtok =
                                          let uu____20833 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20833 in
                                        let env4 =
                                          let uu____20835 =
                                            let uu____20838 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20838 in
                                          push_free_var env3 flid gtok
                                            uu____20835 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20594 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20994 t_norm
                              uu____20996 =
                              match (uu____20994, uu____20996) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21040;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21041;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21069 =
                                    let uu____21076 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____21076 with
                                    | (tcenv',uu____21098,e_t) ->
                                        let uu____21104 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21115 ->
                                              failwith "Impossible" in
                                        (match uu____21104 with
                                         | (e1,t_norm1) ->
                                             ((let uu___356_21131 = env3 in
                                               {
                                                 bindings =
                                                   (uu___356_21131.bindings);
                                                 depth =
                                                   (uu___356_21131.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___356_21131.warn);
                                                 cache =
                                                   (uu___356_21131.cache);
                                                 nolabels =
                                                   (uu___356_21131.nolabels);
                                                 use_zfuel_name =
                                                   (uu___356_21131.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___356_21131.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___356_21131.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____21069 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21146 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21146
                                         then
                                           let uu____21147 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21148 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21149 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21147 uu____21148
                                             uu____21149
                                         else ());
                                        (let uu____21151 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21151 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21188 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21188
                                               then
                                                 let uu____21189 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21190 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21191 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21192 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21189 uu____21190
                                                   uu____21191 uu____21192
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21196 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21196 with
                                               | (vars,guards,env'1,binder_decls,uu____21227)
                                                   ->
                                                   let decl_g =
                                                     let uu____21241 =
                                                       let uu____21252 =
                                                         let uu____21255 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21255 in
                                                       (g, uu____21252,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21241 in
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
                                                     let uu____21280 =
                                                       let uu____21287 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21287) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21280 in
                                                   let gsapp =
                                                     let uu____21297 =
                                                       let uu____21304 =
                                                         let uu____21307 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21307 ::
                                                           vars_tm in
                                                       (g, uu____21304) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21297 in
                                                   let gmax =
                                                     let uu____21313 =
                                                       let uu____21320 =
                                                         let uu____21323 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21323 ::
                                                           vars_tm in
                                                       (g, uu____21320) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21313 in
                                                   let body1 =
                                                     let uu____21329 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21329
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21331 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21331 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21349 =
                                                            let uu____21356 =
                                                              let uu____21357
                                                                =
                                                                let uu____21372
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
                                                                  uu____21372) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21357 in
                                                            let uu____21393 =
                                                              let uu____21396
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21396 in
                                                            (uu____21356,
                                                              uu____21393,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21349 in
                                                        let eqn_f =
                                                          let uu____21400 =
                                                            let uu____21407 =
                                                              let uu____21408
                                                                =
                                                                let uu____21419
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21419) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21408 in
                                                            (uu____21407,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21400 in
                                                        let eqn_g' =
                                                          let uu____21433 =
                                                            let uu____21440 =
                                                              let uu____21441
                                                                =
                                                                let uu____21452
                                                                  =
                                                                  let uu____21453
                                                                    =
                                                                    let uu____21458
                                                                    =
                                                                    let uu____21459
                                                                    =
                                                                    let uu____21466
                                                                    =
                                                                    let uu____21469
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21469
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21466) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21459 in
                                                                    (gsapp,
                                                                    uu____21458) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21453 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21452) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21441 in
                                                            (uu____21440,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21433 in
                                                        let uu____21492 =
                                                          let uu____21501 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21501
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21530)
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
                                                                  let uu____21555
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21555
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21560
                                                                  =
                                                                  let uu____21567
                                                                    =
                                                                    let uu____21568
                                                                    =
                                                                    let uu____21579
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21579) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21568 in
                                                                  (uu____21567,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21560 in
                                                              let uu____21600
                                                                =
                                                                let uu____21607
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21607
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21620
                                                                    =
                                                                    let uu____21623
                                                                    =
                                                                    let uu____21624
                                                                    =
                                                                    let uu____21631
                                                                    =
                                                                    let uu____21632
                                                                    =
                                                                    let uu____21643
                                                                    =
                                                                    let uu____21644
                                                                    =
                                                                    let uu____21649
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21649,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21644 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21643) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21632 in
                                                                    (uu____21631,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21624 in
                                                                    [uu____21623] in
                                                                    (d3,
                                                                    uu____21620) in
                                                              (match uu____21600
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21492
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
                            let uu____21714 =
                              let uu____21727 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21806  ->
                                   fun uu____21807  ->
                                     match (uu____21806, uu____21807) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21962 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21962 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21727 in
                            (match uu____21714 with
                             | (decls2,eqns,env01) ->
                                 let uu____22035 =
                                   let isDeclFun uu___322_22047 =
                                     match uu___322_22047 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22048 -> true
                                     | uu____22059 -> false in
                                   let uu____22060 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____22060
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____22035 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____22100 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___323_22104  ->
                                 match uu___323_22104 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22105 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22111 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22111))) in
                      if uu____22100
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
                   let uu____22163 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22163
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
        let uu____22212 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22212 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22216 = encode_sigelt' env se in
      match uu____22216 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22232 =
                  let uu____22233 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22233 in
                [uu____22232]
            | uu____22234 ->
                let uu____22235 =
                  let uu____22238 =
                    let uu____22239 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22239 in
                  uu____22238 :: g in
                let uu____22240 =
                  let uu____22243 =
                    let uu____22244 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22244 in
                  [uu____22243] in
                FStar_List.append uu____22235 uu____22240 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22257 =
          let uu____22258 = FStar_Syntax_Subst.compress t in
          uu____22258.FStar_Syntax_Syntax.n in
        match uu____22257 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22262)) -> s = "opaque_to_smt"
        | uu____22263 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22268 =
          let uu____22269 = FStar_Syntax_Subst.compress t in
          uu____22269.FStar_Syntax_Syntax.n in
        match uu____22268 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22273)) -> s = "uninterpreted_by_smt"
        | uu____22274 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22279 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22284 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22287 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22290 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22305 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22309 =
            let uu____22310 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22310 Prims.op_Negation in
          if uu____22309
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22336 ->
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
               let uu____22356 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22356 with
               | (aname,atok,env2) ->
                   let uu____22372 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22372 with
                    | (formals,uu____22390) ->
                        let uu____22403 =
                          let uu____22408 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22408 env2 in
                        (match uu____22403 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22420 =
                                 let uu____22421 =
                                   let uu____22432 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22448  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22432,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22421 in
                               [uu____22420;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22461 =
                               let aux uu____22513 uu____22514 =
                                 match (uu____22513, uu____22514) with
                                 | ((bv,uu____22566),(env3,acc_sorts,acc)) ->
                                     let uu____22604 = gen_term_var env3 bv in
                                     (match uu____22604 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22461 with
                              | (uu____22676,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22699 =
                                      let uu____22706 =
                                        let uu____22707 =
                                          let uu____22718 =
                                            let uu____22719 =
                                              let uu____22724 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22724) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22719 in
                                          ([[app]], xs_sorts, uu____22718) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22707 in
                                      (uu____22706,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22699 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22744 =
                                      let uu____22751 =
                                        let uu____22752 =
                                          let uu____22763 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22763) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22752 in
                                      (uu____22751,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22744 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22782 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22782 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22810,uu____22811)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22812 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22812 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22829,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22835 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___324_22839  ->
                      match uu___324_22839 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22840 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22845 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22846 -> false)) in
            Prims.op_Negation uu____22835 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22855 =
               let uu____22862 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22862 env fv t quals in
             match uu____22855 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22877 =
                   let uu____22880 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22880 in
                 (uu____22877, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22888 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22888 with
           | (uu____22897,f1) ->
               let uu____22899 = encode_formula f1 env in
               (match uu____22899 with
                | (f2,decls) ->
                    let g =
                      let uu____22913 =
                        let uu____22914 =
                          let uu____22921 =
                            let uu____22924 =
                              let uu____22925 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22925 in
                            FStar_Pervasives_Native.Some uu____22924 in
                          let uu____22926 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22921, uu____22926) in
                        FStar_SMTEncoding_Util.mkAssume uu____22914 in
                      [uu____22913] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22932) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22944 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22962 =
                       let uu____22965 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22965.FStar_Syntax_Syntax.fv_name in
                     uu____22962.FStar_Syntax_Syntax.v in
                   let uu____22966 =
                     let uu____22967 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22967 in
                   if uu____22966
                   then
                     let val_decl =
                       let uu___359_22995 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___359_22995.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___359_22995.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___359_22995.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____23000 = encode_sigelt' env1 val_decl in
                     match uu____23000 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22944 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23028,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23030;
                          FStar_Syntax_Syntax.lbtyp = uu____23031;
                          FStar_Syntax_Syntax.lbeff = uu____23032;
                          FStar_Syntax_Syntax.lbdef = uu____23033;_}::[]),uu____23034)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23053 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23053 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____23082 =
                   let uu____23085 =
                     let uu____23086 =
                       let uu____23093 =
                         let uu____23094 =
                           let uu____23105 =
                             let uu____23106 =
                               let uu____23111 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23111) in
                             FStar_SMTEncoding_Util.mkEq uu____23106 in
                           ([[b2t_x]], [xx], uu____23105) in
                         FStar_SMTEncoding_Util.mkForall uu____23094 in
                       (uu____23093,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____23086 in
                   [uu____23085] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23082 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23144,uu____23145) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___325_23154  ->
                  match uu___325_23154 with
                  | FStar_Syntax_Syntax.Discriminator uu____23155 -> true
                  | uu____23156 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23159,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23170 =
                     let uu____23171 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23171.FStar_Ident.idText in
                   uu____23170 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___326_23175  ->
                     match uu___326_23175 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23176 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23180) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___327_23197  ->
                  match uu___327_23197 with
                  | FStar_Syntax_Syntax.Projector uu____23198 -> true
                  | uu____23203 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23206 = try_lookup_free_var env l in
          (match uu____23206 with
           | FStar_Pervasives_Native.Some uu____23213 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___360_23217 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___360_23217.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___360_23217.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___360_23217.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23224) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23242) ->
          let uu____23251 = encode_sigelts env ses in
          (match uu____23251 with
           | (g,env1) ->
               let uu____23268 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___328_23291  ->
                         match uu___328_23291 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23292;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23293;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23294;_}
                             -> false
                         | uu____23297 -> true)) in
               (match uu____23268 with
                | (g',inversions) ->
                    let uu____23312 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___329_23333  ->
                              match uu___329_23333 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23334 ->
                                  true
                              | uu____23345 -> false)) in
                    (match uu____23312 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23363,tps,k,uu____23366,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___330_23383  ->
                    match uu___330_23383 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23384 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23393 = c in
              match uu____23393 with
              | (name,args,uu____23398,uu____23399,uu____23400) ->
                  let uu____23405 =
                    let uu____23406 =
                      let uu____23417 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23434  ->
                                match uu____23434 with
                                | (uu____23441,sort,uu____23443) -> sort)) in
                      (name, uu____23417, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23406 in
                  [uu____23405]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23470 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23476 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23476 FStar_Option.isNone)) in
            if uu____23470
            then []
            else
              (let uu____23508 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23508 with
               | (xxsym,xx) ->
                   let uu____23517 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23556  ->
                             fun l  ->
                               match uu____23556 with
                               | (out,decls) ->
                                   let uu____23576 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23576 with
                                    | (uu____23587,data_t) ->
                                        let uu____23589 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23589 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23635 =
                                                 let uu____23636 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23636.FStar_Syntax_Syntax.n in
                                               match uu____23635 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23647,indices) ->
                                                   indices
                                               | uu____23669 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23693  ->
                                                         match uu____23693
                                                         with
                                                         | (x,uu____23699) ->
                                                             let uu____23700
                                                               =
                                                               let uu____23701
                                                                 =
                                                                 let uu____23708
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23708,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23701 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23700)
                                                    env) in
                                             let uu____23711 =
                                               encode_args indices env1 in
                                             (match uu____23711 with
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
                                                      let uu____23737 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23753
                                                                 =
                                                                 let uu____23758
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23758,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23753)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23737
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23761 =
                                                      let uu____23762 =
                                                        let uu____23767 =
                                                          let uu____23768 =
                                                            let uu____23773 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23773,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23768 in
                                                        (out, uu____23767) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23762 in
                                                    (uu____23761,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23517 with
                    | (data_ax,decls) ->
                        let uu____23786 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23786 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23797 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23797 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23801 =
                                 let uu____23808 =
                                   let uu____23809 =
                                     let uu____23820 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23835 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23820,
                                       uu____23835) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23809 in
                                 let uu____23850 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23808,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23850) in
                               FStar_SMTEncoding_Util.mkAssume uu____23801 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23853 =
            let uu____23866 =
              let uu____23867 = FStar_Syntax_Subst.compress k in
              uu____23867.FStar_Syntax_Syntax.n in
            match uu____23866 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23912 -> (tps, k) in
          (match uu____23853 with
           | (formals,res) ->
               let uu____23935 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23935 with
                | (formals1,res1) ->
                    let uu____23946 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23946 with
                     | (vars,guards,env',binder_decls,uu____23971) ->
                         let uu____23984 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23984 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____24003 =
                                  let uu____24010 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____24010) in
                                FStar_SMTEncoding_Util.mkApp uu____24003 in
                              let uu____24019 =
                                let tname_decl =
                                  let uu____24029 =
                                    let uu____24030 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24062  ->
                                              match uu____24062 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____24075 = varops.next_id () in
                                    (tname, uu____24030,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24075, false) in
                                  constructor_or_logic_type_decl uu____24029 in
                                let uu____24084 =
                                  match vars with
                                  | [] ->
                                      let uu____24097 =
                                        let uu____24098 =
                                          let uu____24101 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____24101 in
                                        push_free_var env1 t tname
                                          uu____24098 in
                                      ([], uu____24097)
                                  | uu____24108 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24117 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24117 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24131 =
                                          let uu____24138 =
                                            let uu____24139 =
                                              let uu____24154 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24154) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24139 in
                                          (uu____24138,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24131 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____24084 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____24019 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24194 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24194 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24212 =
                                               let uu____24213 =
                                                 let uu____24220 =
                                                   let uu____24221 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24221 in
                                                 (uu____24220,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24213 in
                                             [uu____24212]
                                           else [] in
                                         let uu____24225 =
                                           let uu____24228 =
                                             let uu____24231 =
                                               let uu____24232 =
                                                 let uu____24239 =
                                                   let uu____24240 =
                                                     let uu____24251 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24251) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24240 in
                                                 (uu____24239,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24232 in
                                             [uu____24231] in
                                           FStar_List.append karr uu____24228 in
                                         FStar_List.append decls1 uu____24225 in
                                   let aux =
                                     let uu____24267 =
                                       let uu____24270 =
                                         inversion_axioms tapp vars in
                                       let uu____24273 =
                                         let uu____24276 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24276] in
                                       FStar_List.append uu____24270
                                         uu____24273 in
                                     FStar_List.append kindingAx uu____24267 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24283,uu____24284,uu____24285,uu____24286,uu____24287)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24295,t,uu____24297,n_tps,uu____24299) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24307 = new_term_constant_and_tok_from_lid env d in
          (match uu____24307 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24324 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24324 with
                | (formals,t_res) ->
                    let uu____24359 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24359 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24373 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24373 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24443 =
                                            mk_term_projector_name d x in
                                          (uu____24443,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24445 =
                                  let uu____24464 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24464, true) in
                                FStar_All.pipe_right uu____24445
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
                              let uu____24503 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24503 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24515::uu____24516 ->
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
                                         let uu____24561 =
                                           let uu____24572 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24572) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24561
                                     | uu____24597 -> tok_typing in
                                   let uu____24606 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24606 with
                                    | (vars',guards',env'',decls_formals,uu____24631)
                                        ->
                                        let uu____24644 =
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
                                        (match uu____24644 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24675 ->
                                                   let uu____24682 =
                                                     let uu____24683 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24683 in
                                                   [uu____24682] in
                                             let encode_elim uu____24693 =
                                               let uu____24694 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24694 with
                                               | (head1,args) ->
                                                   let uu____24737 =
                                                     let uu____24738 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24738.FStar_Syntax_Syntax.n in
                                                   (match uu____24737 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24748;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24749;_},uu____24750)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24756 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24756
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
                                                                 | uu____24799
                                                                    ->
                                                                    let uu____24800
                                                                    =
                                                                    let uu____24801
                                                                    =
                                                                    let uu____24806
                                                                    =
                                                                    let uu____24807
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24807 in
                                                                    (uu____24806,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24801 in
                                                                    FStar_Exn.raise
                                                                    uu____24800 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24823
                                                                    =
                                                                    let uu____24824
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24824 in
                                                                    if
                                                                    uu____24823
                                                                    then
                                                                    let uu____24837
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24837]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24839
                                                               =
                                                               let uu____24852
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24902
                                                                     ->
                                                                    fun
                                                                    uu____24903
                                                                     ->
                                                                    match 
                                                                    (uu____24902,
                                                                    uu____24903)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24998
                                                                    =
                                                                    let uu____25005
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25005 in
                                                                    (match uu____24998
                                                                    with
                                                                    | 
                                                                    (uu____25018,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25026
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25026
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25028
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25028
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
                                                                 uu____24852 in
                                                             (match uu____24839
                                                              with
                                                              | (uu____25043,arg_vars,elim_eqns_or_guards,uu____25046)
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
                                                                    let uu____25076
                                                                    =
                                                                    let uu____25083
                                                                    =
                                                                    let uu____25084
                                                                    =
                                                                    let uu____25095
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25106
                                                                    =
                                                                    let uu____25107
                                                                    =
                                                                    let uu____25112
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25112) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25107 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25095,
                                                                    uu____25106) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25084 in
                                                                    (uu____25083,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25076 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25135
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25135,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25137
                                                                    =
                                                                    let uu____25144
                                                                    =
                                                                    let uu____25145
                                                                    =
                                                                    let uu____25156
                                                                    =
                                                                    let uu____25161
                                                                    =
                                                                    let uu____25164
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25164] in
                                                                    [uu____25161] in
                                                                    let uu____25169
                                                                    =
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25175
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25176
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25175,
                                                                    uu____25176) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25170 in
                                                                    (uu____25156,
                                                                    [x],
                                                                    uu____25169) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25145 in
                                                                    let uu____25195
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25144,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25195) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25137
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25202
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
                                                                    (let uu____25230
                                                                    =
                                                                    let uu____25231
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25231
                                                                    dapp1 in
                                                                    [uu____25230]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25202
                                                                    FStar_List.flatten in
                                                                    let uu____25238
                                                                    =
                                                                    let uu____25245
                                                                    =
                                                                    let uu____25246
                                                                    =
                                                                    let uu____25257
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25268
                                                                    =
                                                                    let uu____25269
                                                                    =
                                                                    let uu____25274
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25274) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25269 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25257,
                                                                    uu____25268) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25246 in
                                                                    (uu____25245,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25238) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25295 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25295
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
                                                                 | uu____25338
                                                                    ->
                                                                    let uu____25339
                                                                    =
                                                                    let uu____25340
                                                                    =
                                                                    let uu____25345
                                                                    =
                                                                    let uu____25346
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25346 in
                                                                    (uu____25345,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25340 in
                                                                    FStar_Exn.raise
                                                                    uu____25339 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25362
                                                                    =
                                                                    let uu____25363
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25363 in
                                                                    if
                                                                    uu____25362
                                                                    then
                                                                    let uu____25376
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25376]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25378
                                                               =
                                                               let uu____25391
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25441
                                                                     ->
                                                                    fun
                                                                    uu____25442
                                                                     ->
                                                                    match 
                                                                    (uu____25441,
                                                                    uu____25442)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25537
                                                                    =
                                                                    let uu____25544
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25544 in
                                                                    (match uu____25537
                                                                    with
                                                                    | 
                                                                    (uu____25557,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25565
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25565
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25567
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25567
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
                                                                 uu____25391 in
                                                             (match uu____25378
                                                              with
                                                              | (uu____25582,arg_vars,elim_eqns_or_guards,uu____25585)
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
                                                                    let uu____25615
                                                                    =
                                                                    let uu____25622
                                                                    =
                                                                    let uu____25623
                                                                    =
                                                                    let uu____25634
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25645
                                                                    =
                                                                    let uu____25646
                                                                    =
                                                                    let uu____25651
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25651) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25646 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25634,
                                                                    uu____25645) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25623 in
                                                                    (uu____25622,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25615 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25674
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25674,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25676
                                                                    =
                                                                    let uu____25683
                                                                    =
                                                                    let uu____25684
                                                                    =
                                                                    let uu____25695
                                                                    =
                                                                    let uu____25700
                                                                    =
                                                                    let uu____25703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25703] in
                                                                    [uu____25700] in
                                                                    let uu____25708
                                                                    =
                                                                    let uu____25709
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25715
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25714,
                                                                    uu____25715) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25709 in
                                                                    (uu____25695,
                                                                    [x],
                                                                    uu____25708) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25684 in
                                                                    let uu____25734
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25683,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25734) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25676
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25741
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
                                                                    (let uu____25769
                                                                    =
                                                                    let uu____25770
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25770
                                                                    dapp1 in
                                                                    [uu____25769]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25741
                                                                    FStar_List.flatten in
                                                                    let uu____25777
                                                                    =
                                                                    let uu____25784
                                                                    =
                                                                    let uu____25785
                                                                    =
                                                                    let uu____25796
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25807
                                                                    =
                                                                    let uu____25808
                                                                    =
                                                                    let uu____25813
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25813) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25808 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25796,
                                                                    uu____25807) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25785 in
                                                                    (uu____25784,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25777) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25832 ->
                                                        ((let uu____25834 =
                                                            let uu____25835 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25836 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25835
                                                              uu____25836 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25834);
                                                         ([], []))) in
                                             let uu____25841 = encode_elim () in
                                             (match uu____25841 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25861 =
                                                      let uu____25864 =
                                                        let uu____25867 =
                                                          let uu____25870 =
                                                            let uu____25873 =
                                                              let uu____25874
                                                                =
                                                                let uu____25885
                                                                  =
                                                                  let uu____25888
                                                                    =
                                                                    let uu____25889
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25889 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25888 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25885) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25874 in
                                                            [uu____25873] in
                                                          let uu____25894 =
                                                            let uu____25897 =
                                                              let uu____25900
                                                                =
                                                                let uu____25903
                                                                  =
                                                                  let uu____25906
                                                                    =
                                                                    let uu____25909
                                                                    =
                                                                    let uu____25912
                                                                    =
                                                                    let uu____25913
                                                                    =
                                                                    let uu____25920
                                                                    =
                                                                    let uu____25921
                                                                    =
                                                                    let uu____25932
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25932) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25921 in
                                                                    (uu____25920,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25913 in
                                                                    let uu____25945
                                                                    =
                                                                    let uu____25948
                                                                    =
                                                                    let uu____25949
                                                                    =
                                                                    let uu____25956
                                                                    =
                                                                    let uu____25957
                                                                    =
                                                                    let uu____25968
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25979
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25968,
                                                                    uu____25979) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25957 in
                                                                    (uu____25956,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25949 in
                                                                    [uu____25948] in
                                                                    uu____25912
                                                                    ::
                                                                    uu____25945 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25909 in
                                                                  FStar_List.append
                                                                    uu____25906
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25903 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25900 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25897 in
                                                          FStar_List.append
                                                            uu____25870
                                                            uu____25894 in
                                                        FStar_List.append
                                                          decls3 uu____25867 in
                                                      FStar_List.append
                                                        decls2 uu____25864 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25861 in
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
           (fun uu____26025  ->
              fun se  ->
                match uu____26025 with
                | (g,env1) ->
                    let uu____26045 = encode_sigelt env1 se in
                    (match uu____26045 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26102 =
        match uu____26102 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26134 ->
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
                 ((let uu____26140 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26140
                   then
                     let uu____26141 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26142 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26143 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26141 uu____26142 uu____26143
                   else ());
                  (let uu____26145 = encode_term t1 env1 in
                   match uu____26145 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26161 =
                         let uu____26168 =
                           let uu____26169 =
                             let uu____26170 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26170
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26169 in
                         new_term_constant_from_string env1 x uu____26168 in
                       (match uu____26161 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26186 = FStar_Options.log_queries () in
                              if uu____26186
                              then
                                let uu____26189 =
                                  let uu____26190 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26191 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26192 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26190 uu____26191 uu____26192 in
                                FStar_Pervasives_Native.Some uu____26189
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26208,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26222 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26222 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26245,se,uu____26247) ->
                 let uu____26252 = encode_sigelt env1 se in
                 (match uu____26252 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26269,se) ->
                 let uu____26275 = encode_sigelt env1 se in
                 (match uu____26275 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26292 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26292 with | (uu____26315,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26327 'Auu____26328 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26328,'Auu____26327)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26396  ->
              match uu____26396 with
              | (l,uu____26408,uu____26409) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26455  ->
              match uu____26455 with
              | (l,uu____26469,uu____26470) ->
                  let uu____26479 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26480 =
                    let uu____26483 =
                      let uu____26484 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26484 in
                    [uu____26483] in
                  uu____26479 :: uu____26480)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26505 =
      let uu____26508 =
        let uu____26509 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26512 =
          let uu____26513 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26513 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26509;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26512
        } in
      [uu____26508] in
    FStar_ST.op_Colon_Equals last_env uu____26505
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26572 = FStar_ST.op_Bang last_env in
      match uu____26572 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26628 ->
          let uu___361_26631 = e in
          let uu____26632 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___361_26631.bindings);
            depth = (uu___361_26631.depth);
            tcenv;
            warn = (uu___361_26631.warn);
            cache = (uu___361_26631.cache);
            nolabels = (uu___361_26631.nolabels);
            use_zfuel_name = (uu___361_26631.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___361_26631.encode_non_total_function_typ);
            current_module_name = uu____26632
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26636 = FStar_ST.op_Bang last_env in
    match uu____26636 with
    | [] -> failwith "Empty env stack"
    | uu____26691::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26749  ->
    let uu____26750 = FStar_ST.op_Bang last_env in
    match uu____26750 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___362_26813 = hd1 in
          {
            bindings = (uu___362_26813.bindings);
            depth = (uu___362_26813.depth);
            tcenv = (uu___362_26813.tcenv);
            warn = (uu___362_26813.warn);
            cache = refs;
            nolabels = (uu___362_26813.nolabels);
            use_zfuel_name = (uu___362_26813.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___362_26813.encode_non_total_function_typ);
            current_module_name = (uu___362_26813.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26868  ->
    let uu____26869 = FStar_ST.op_Bang last_env in
    match uu____26869 with
    | [] -> failwith "Popping an empty stack"
    | uu____26924::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____27017::uu____27018,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___363_27026 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___363_27026.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___363_27026.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___363_27026.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27027 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____27042 =
        let uu____27045 =
          let uu____27046 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____27046 in
        let uu____27047 = open_fact_db_tags env in uu____27045 :: uu____27047 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27042
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
      let uu____27069 = encode_sigelt env se in
      match uu____27069 with
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
        let uu____27105 = FStar_Options.log_queries () in
        if uu____27105
        then
          let uu____27108 =
            let uu____27109 =
              let uu____27110 =
                let uu____27111 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____27111 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____27110 in
            FStar_SMTEncoding_Term.Caption uu____27109 in
          uu____27108 :: decls
        else decls in
      (let uu____27122 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27122
       then
         let uu____27123 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27123
       else ());
      (let env =
         let uu____27126 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____27126 tcenv in
       let uu____27127 = encode_top_level_facts env se in
       match uu____27127 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27141 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____27141)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27153 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27153
       then
         let uu____27154 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27154
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27189  ->
                 fun se  ->
                   match uu____27189 with
                   | (g,env2) ->
                       let uu____27209 = encode_top_level_facts env2 se in
                       (match uu____27209 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27232 =
         encode_signature
           (let uu___364_27241 = env in
            {
              bindings = (uu___364_27241.bindings);
              depth = (uu___364_27241.depth);
              tcenv = (uu___364_27241.tcenv);
              warn = false;
              cache = (uu___364_27241.cache);
              nolabels = (uu___364_27241.nolabels);
              use_zfuel_name = (uu___364_27241.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___364_27241.encode_non_total_function_typ);
              current_module_name = (uu___364_27241.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27232 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27258 = FStar_Options.log_queries () in
             if uu____27258
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___365_27266 = env1 in
               {
                 bindings = (uu___365_27266.bindings);
                 depth = (uu___365_27266.depth);
                 tcenv = (uu___365_27266.tcenv);
                 warn = true;
                 cache = (uu___365_27266.cache);
                 nolabels = (uu___365_27266.nolabels);
                 use_zfuel_name = (uu___365_27266.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___365_27266.encode_non_total_function_typ);
                 current_module_name = (uu___365_27266.current_module_name)
               });
            (let uu____27268 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27268
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
        (let uu____27320 =
           let uu____27321 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27321.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27320);
        (let env =
           let uu____27323 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27323 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27335 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27370 = aux rest in
                 (match uu____27370 with
                  | (out,rest1) ->
                      let t =
                        let uu____27400 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27400 with
                        | FStar_Pervasives_Native.Some uu____27405 ->
                            let uu____27406 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27406
                              x.FStar_Syntax_Syntax.sort
                        | uu____27407 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27411 =
                        let uu____27414 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___366_27417 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___366_27417.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___366_27417.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27414 :: out in
                      (uu____27411, rest1))
             | uu____27422 -> ([], bindings1) in
           let uu____27429 = aux bindings in
           match uu____27429 with
           | (closing,bindings1) ->
               let uu____27454 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27454, bindings1) in
         match uu____27335 with
         | (q1,bindings1) ->
             let uu____27477 =
               let uu____27482 =
                 FStar_List.filter
                   (fun uu___331_27487  ->
                      match uu___331_27487 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27488 ->
                          false
                      | uu____27495 -> true) bindings1 in
               encode_env_bindings env uu____27482 in
             (match uu____27477 with
              | (env_decls,env1) ->
                  ((let uu____27513 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27513
                    then
                      let uu____27514 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27514
                    else ());
                   (let uu____27516 = encode_formula q1 env1 in
                    match uu____27516 with
                    | (phi,qdecls) ->
                        let uu____27537 =
                          let uu____27542 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27542 phi in
                        (match uu____27537 with
                         | (labels,phi1) ->
                             let uu____27559 = encode_labels labels in
                             (match uu____27559 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27596 =
                                      let uu____27603 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27604 =
                                        varops.mk_unique "@query" in
                                      (uu____27603,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27604) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27596 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))